import re
import time
import difflib
import os, json, base64, secrets, hashlib, urllib.request, urllib.parse, urllib.error, threading
from datetime import datetime, timezone, timedelta, date
# Android ships no CA bundle that Python's ssl module can find, so every HTTPS call (licence, support,
# cloud sync) would fail with CERTIFICATE_VERIFY_FAILED. 'certifi' (listed in buildozer.spec) provides one.
try:
    import certifi
    _ca = certifi.where()
    # Only use the bundle if the file really exists inside the APK; a wrong path would break ALL HTTPS.
    if _ca and os.path.isfile(_ca) and os.path.getsize(_ca) > 1000:
        os.environ.setdefault("SSL_CERT_FILE", _ca)
except Exception:
    pass
APP_NAME="Shop Management"; APP_VERSION="2.5.0-CAPITAL"
SYNC_INTERVAL_SECONDS=45
SYNC_BATCH_SIZE=100
PUBLIC_KEY_PEM = """-----BEGIN PUBLIC KEY-----
MIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEA2CasjqOeIdXEzSI0GrHA
8i3nzGyaIsuqSQaa3Qpc04X8fqWe4pzoIai99mcabf/Y1iVNtvaM280iWv3gcXkJ
50Kc7jklaKFnp+ZGdXaWFFQBRY5+gqPelsQXm5QWMJXFZxCdkmJVw53wMdiOm0LS
DTsLb6gurAIiJH/goRkJIZ7g1y2SSFLR0h4lFEcao+nRUy4rGLT/DYDjqdSUiFAX
ZNaOPZtckAlMzx+SFQRDyCDI4fnrZRlFijbOA9WJFXgDvmJbtv+DbhuAJWRJn8Gz
C2c+gmTyepmYq6RvDKWOlGGkNKpn0wv9AXlDh4tNshK2Htu6M46M4SOzBrkSvtLM
bwIDAQAB
-----END PUBLIC KEY-----
"""
UNITS=["Piece","Packet","Box","Bottle","Pair","Dozen","Set","kg","g","Litre","ml","Metre","Roll","Custom"]
DEPARTMENTS=["Scholastic Materials","Beauty & Cosmetics","Food & Beverages","Household","Electronics","Clothing","Hardware","Other"]
DEFAULT_CATEGORIES=["Groceries","Electronics","Clothing","Hardware","Stationery","Beauty & Cosmetics","Household","Beverages","Other"]
def data_path(name):
    try:
        from kivy.app import App; base=App.get_running_app().user_data_dir
    except Exception: base=os.path.join(os.path.expanduser("~"),".shop_management_v2")
    os.makedirs(base,exist_ok=True); return os.path.join(base,name)
_FILE_LOCK=threading.RLock()   # the UI thread and the sync thread both write JSON files
def load_json(name,default):
    p=data_path(name)
    try:
        with open(p,"r",encoding="utf-8") as f:return json.load(f)
    except FileNotFoundError:
        return default
    except ValueError:
        # The file exists but is damaged. Keep a copy instead of letting the next save overwrite
        # it with an empty default (which would silently erase the shop's records).
        try:
            with _FILE_LOCK:
                if os.path.exists(p):
                    os.replace(p,p+".corrupt-"+datetime.now().strftime("%Y%m%d%H%M%S"))
        except Exception:pass
        return default
    except Exception:return default
def save_json(name,value):
    p=data_path(name)
    with _FILE_LOCK:
        tmp=p+".tmp"
        with open(tmp,"w",encoding="utf-8") as f:
            json.dump(value,f,indent=2,ensure_ascii=False)
            f.flush()
            try:os.fsync(f.fileno())
            except Exception:pass
        os.replace(tmp,p)
_DEVICE_ID_CACHE=[None]
def device_id():
    if _DEVICE_ID_CACHE[0]:return _DEVICE_ID_CACHE[0]
    try:
        from jnius import autoclass
        S=autoclass("android.provider.Settings$Secure"); A=autoclass("org.kivy.android.PythonActivity")
        v=S.getString(A.mActivity.getContentResolver(),S.ANDROID_ID)
        if v:
            _DEVICE_ID_CACHE[0]="ANDROID-"+str(v).strip()
            return _DEVICE_ID_CACHE[0]
    except Exception:pass
    p=data_path("installation_id.txt")
    try:
        with open(p,encoding="utf-8") as f:v=f.read().strip()
        if v:
            _DEVICE_ID_CACHE[0]=v
            return v
    except Exception:pass
    v="INSTALL-"+secrets.token_hex(12).upper()
    try:
        with open(p,"w",encoding="utf-8") as f:f.write(v)
    except Exception:pass
    _DEVICE_ID_CACHE[0]=v
    return v
def make_device_request():
    raw=json.dumps({"version":1,"device_id":device_id()},separators=(",",":"),sort_keys=True).encode()
    return base64.urlsafe_b64encode(raw).decode().rstrip("=")
def _der_read(buf,pos):
    """Read one DER element -> (tag, content_start, content_end)."""
    tag=buf[pos]; ln=buf[pos+1]; pos+=2
    if ln & 0x80:
        n=ln & 0x7F
        if n==0 or n>4:raise ValueError("bad DER length")
        ln=int.from_bytes(buf[pos:pos+n],"big"); pos+=n
    if pos+ln>len(buf):raise ValueError("truncated DER")
    return tag,pos,pos+ln
def _rsa_public_numbers(pem):
    """(n, e) from a PEM 'SubjectPublicKeyInfo' RSA public key."""
    body="".join(l for l in pem.strip().splitlines() if not l.startswith("-----"))
    der=base64.b64decode(body)
    t,s,e=_der_read(der,0)                       # SEQUENCE { algorithm, BIT STRING }
    if t!=0x30:raise ValueError("bad public key")
    t,s2,e2=_der_read(der,s)                     # AlgorithmIdentifier
    t,s3,e3=_der_read(der,e2)                    # BIT STRING
    if t!=0x03:raise ValueError("bad public key")
    inner=der[s3+1:e3]                           # skip the 'unused bits' byte
    t,s4,e4=_der_read(inner,0)                   # RSAPublicKey SEQUENCE
    if t!=0x30:raise ValueError("bad public key")
    t,a,b=_der_read(inner,s4);n=int.from_bytes(inner[a:b],"big")
    t,c,d=_der_read(inner,b);ev=int.from_bytes(inner[c:d],"big")
    return n,ev
_SHA256_PREFIX=bytes.fromhex("3031300d060960864801650304020105000420")
def rsa_verify_sha256(pem,signature,message):
    """True only when 'signature' is a valid RSASSA-PKCS1-v1_5 SHA-256 signature of 'message'.
    Strict: the whole encoded block is rebuilt and compared, so malformed padding is rejected."""
    n,e=_rsa_public_numbers(pem)
    k=(n.bit_length()+7)//8
    if len(signature)!=k:return False
    s=int.from_bytes(signature,"big")
    if s>=n:return False
    em=pow(s,e,n).to_bytes(k,"big")
    t=_SHA256_PREFIX+hashlib.sha256(message).digest()
    if k<len(t)+11:return False
    expected=b"\x00\x01"+b"\xff"*(k-len(t)-3)+b"\x00"+t
    return secrets.compare_digest(em,expected)

def verify_license(code, now=None):
    try:
        code=str(code or "").strip()
        if code.count(".") != 1:
            return False,"Invalid license format. Expected signed activation code."
        a,b=code.split(".",1)
        if not a or not b:
            return False,"Invalid license format. Expected signed activation code."
        raw=base64.urlsafe_b64decode(a+"="*((4-len(a)%4)%4))
        sig=base64.urlsafe_b64decode(b+"="*((4-len(b)%4)%4))
        if not rsa_verify_sha256(PUBLIC_KEY_PEM,sig,raw):
            return False,"Invalid license: SIGNATURE DOES NOT MATCH THE SHOP APP PUBLIC KEY"
        p=json.loads(raw.decode())
        if str(p.get("device_id",""))!=device_id():return False,"License belongs to another device"
        if int(p.get("version",0))!=1:return False,"Unsupported license version"
        exp=datetime.fromisoformat(p["expires_at"].replace("Z","+00:00"))
        if exp.tzinfo is None:exp=exp.replace(tzinfo=timezone.utc)   # naive timestamps would crash the comparison
        if exp<=(now or datetime.now(timezone.utc)):return False,"License has expired"
        return True,p
    except Exception as e:
        return False,"Invalid license: "+str(e)

# ================= ONLINE LICENSING / SUPPORT =================
# Put only the Supabase PROJECT URL and PUBLISHABLE/ANON key here.
# Never put the Supabase secret/service_role key in the Shop App.
# ONLINE SERVICE CONFIGURATION
# Supabase project URL for the Shop Management licensing project.
SUPABASE_URL = "https://pthgerewoemoqoztchwb.supabase.co"

# IMPORTANT:
# Paste your Supabase PUBLISHABLE key (or legacy anon key) between the quotes below.
# Do NOT paste the secret/service_role key here.
SUPABASE_PUBLISHABLE_KEY = "sb_publishable_cyLGgwZOVQLJjIGCC2g98Q_gW9u_lCw"


_SERVER_DATE=[None]    # the server's own clock, taken from the last HTTPS response

_SSL_CTX=[None]
_SSL_INFO=[""]
def _ssl_context():
    """HTTPS context that really has trusted CA certificates on Android.
    python-for-android's Python cannot find Android's certificate store by itself, which makes every
    request fail with CERTIFICATE_VERIFY_FAILED. We load, in order: the certifi bundle, then the phone's own
    system certificates. Verification stays ON; if nothing can be loaded the request fails safely."""
    if _SSL_CTX[0] is not None:return _SSL_CTX[0]
    import ssl
    ctx=ssl.create_default_context()
    used=[]
    try:
        import certifi
        ca=certifi.where()
        if ca and os.path.isfile(ca):
            ctx.load_verify_locations(cafile=ca); used.append("certifi")
    except Exception:pass
    pem_re=re.compile(r"-----BEGIN CERTIFICATE-----.*?-----END CERTIFICATE-----",re.S)
    for d in ("/apex/com.android.conscrypt/cacerts","/system/etc/security/cacerts","/etc/ssl/certs"):
        try:
            if not os.path.isdir(d):continue
            blocks=[]
            for name in os.listdir(d):
                fp=os.path.join(d,name)
                if os.path.isfile(fp):
                    with open(fp,"r",encoding="utf-8",errors="ignore") as f:blocks+=pem_re.findall(f.read())
            if blocks:
                ctx.load_verify_locations(cadata="\n".join(blocks)); used.append(os.path.basename(d.rstrip("/")))
        except Exception:pass
    try:n=ctx.cert_store_stats().get("x509_ca",0)
    except Exception:n=0
    _SSL_INFO[0]="CA certificates: %d (from %s)"%(n,", ".join(used) or "nowhere")
    _SSL_CTX[0]=ctx
    return ctx

def online_configured():
    return (SUPABASE_URL.startswith("https://") and
            "PASTE_YOUR" not in SUPABASE_URL and
            SUPABASE_PUBLISHABLE_KEY and "PASTE_YOUR" not in SUPABASE_PUBLISHABLE_KEY)


def supa_request(path, method="GET", body=None):
    """Safe Supabase HTTP helper. Never let an online error close the app."""
    if not online_configured():
        raise RuntimeError("Online licensing is not configured yet.")
    url=SUPABASE_URL.rstrip("/") + path
    data=None if body is None else json.dumps(body,ensure_ascii=False).encode("utf-8")
    req=urllib.request.Request(url,data=data,method=method)
    req.add_header("apikey",SUPABASE_PUBLISHABLE_KEY)
    req.add_header("Authorization","Bearer "+SUPABASE_PUBLISHABLE_KEY)
    req.add_header("Content-Type","application/json")
    req.add_header("Accept","application/json")
    req.add_header("Prefer","return=representation")
    try:
        with urllib.request.urlopen(req,timeout=15,context=_ssl_context()) as response:
            try:
                from email.utils import parsedate_to_datetime
                _SERVER_DATE[0]=parsedate_to_datetime(response.headers.get("Date")).astimezone(timezone.utc)
            except Exception:pass
            raw=response.read().decode("utf-8",errors="replace").strip()
            if not raw:return None
            try:return json.loads(raw)
            except json.JSONDecodeError:return raw
    except urllib.error.HTTPError as e:
        try: detail=e.read().decode("utf-8",errors="replace").strip()
        except Exception: detail=""
        if detail:raise RuntimeError(f"Server HTTP {e.code}: {detail[:500]}")
        raise RuntimeError(f"Server HTTP {e.code}: {e.reason}")
    except urllib.error.URLError as e:
        why=str(getattr(e,"reason",e))
        if "CERTIFICATE_VERIFY" in why:why+="  ["+_SSL_INFO[0]+"]"
        raise RuntimeError("Network error: "+why)
    except TimeoutError:
        raise RuntimeError("Online request timed out.")
    except Exception as e:
        raise RuntimeError("Online request failed: "+str(e))



def cached_support():
    return load_json("support_cache.json", {
        "name":"", "phone":"", "whatsapp":"", "email":"", "hours":"",
        "message":"For activation, renewal, payment or technical assistance, please contact support.",
        "updated_at":""
    })


def fetch_support_online():
    rows = supa_request("/rest/v1/support_info?id=eq.1&select=*")
    if not rows:
        raise RuntimeError("No support information published yet.")
    data = dict(rows[0])
    save_json("support_cache.json", data)
    return data


# ================= LICENCE GATE =================
# The app is usable ONLY while license_status() says "ok":
#   * a developer-signed licence for THIS phone that has not expired, or
#   * a cloud registration made with a valid join code whose licence has not expired
#     (or, if the server gave no expiry date, that the server has confirmed within OFFLINE_GRACE_DAYS), and
#   * the server has not withdrawn this phone.
# Anything else locks the app on the licence screen until a new licence / join code is obtained.
LICENSE_STATE_FILE="license_state.json"
OFFLINE_GRACE_DAYS=7
STARTUP_RECHECK_HOURS=12
REVOKED_WORDS=("revoked","blocked","disabled","suspended","expired","inactive")

def _parse_iso(v):
    try:
        d=datetime.fromisoformat(str(v).replace("Z","+00:00"))
        return d if d.tzinfo else d.replace(tzinfo=timezone.utc)
    except Exception:return None

def _license_state():
    s=load_json(LICENSE_STATE_FILE,{})
    return s if isinstance(s,dict) else {}

def license_state_update(**kw):
    s=_license_state(); s.update(kw); save_json(LICENSE_STATE_FILE,s); return s

def _license_now():
    """Current time that can never run backwards: setting the phone's clock back does not extend a licence."""
    real=datetime.now(timezone.utc); s=_license_state(); seen=_parse_iso(s.get("max_seen"))
    if seen and seen>real:return seen
    if (not seen) or (real-seen)>timedelta(seconds=30):
        try:license_state_update(max_seen=real.isoformat())
        except Exception:pass
    return real

def _peek_payload(code):
    try:
        a=str(code).split(".")[0]
        return json.loads(base64.urlsafe_b64decode(a+"="*((4-len(a)%4)%4)).decode())
    except Exception:return {}

def _fmt_day(d):
    try:return d.astimezone().strftime("%d %b %Y")
    except Exception:return str(d)

def license_status():
    """-> (state, message, expiry). state is one of: ok, expired, revoked, unverified, none."""
    now=_license_now(); st=_license_state()
    note="\n(Phone date: "+_fmt_day(now)+" - if this is wrong, correct it in Settings.)"
    if st.get("revoked"):
        return "revoked",str(st.get("revoked_reason") or "Access for this phone was withdrawn.")+"\nRequest a new licence, or join the business again with a new code.",None
    saved=load_saved_license()
    if saved:
        code=saved.get("code","")
        ok,p=verify_license(code,now)
        if ok:
            return "ok","LICENSE VALID\nBusiness: "+str(p.get("business_name",""))+"\nExpires: "+str(p.get("expires_at","")),_parse_iso(p.get("expires_at"))
        if "expired" in str(p).lower():
            pl=_peek_payload(code)
            return "expired","YOUR LICENSE HAS EXPIRED ("+_fmt_day(_parse_iso(pl.get("expires_at")) or now)+")\nBusiness: "+str(pl.get("business_name",""))+"\nRequest a renewal from the developer to continue."+note,_parse_iso(pl.get("expires_at"))
    reg=_cloud_registration()
    if reg:
        exp=_parse_iso(reg.get("expires_at")); name=str(reg.get("business_name") or "")
        if exp:
            if exp<=now:
                return "expired","THE BUSINESS LICENSE HAS EXPIRED ("+_fmt_day(exp)+")\nBusiness: "+name+"\nAsk the owner to renew, then check again."+note,exp
            return "ok","LICENSE VALID\nBusiness: "+name+"\nExpires: "+str(reg.get("expires_at")),exp
        last=_parse_iso(st.get("last_online_ok"))
        if last and now-last<=timedelta(days=OFFLINE_GRACE_DAYS):
            return "ok","LICENSE CONFIRMED ONLINE\nBusiness: "+name,None
        return "unverified","This phone must connect to the internet to confirm its licence.\nBusiness: "+name,None
    return "none","No valid business registration found. Request activation for a new business, or join an existing business with a joining code.",None

def make_request_token():
    return secrets.token_urlsafe(32)


def submit_online_request(business_name, contact, kind="activation"):
    business_name=str(business_name or "").strip()
    contact=str(contact or "").strip()
    if not business_name:
        raise ValueError("Business name is required.")
    if not contact:
        raise ValueError("Contact number is required.")
    token=make_request_token()
    req_code=make_device_request()
    result=supa_request("/rest/v1/rpc/submit_activation_request", "POST", {
        "p_request_token":token, "p_device_id":device_id(),
        "p_request_code":req_code, "p_request_kind":kind,
        "p_business_name":business_name, "p_contact":contact
    })
    save_json("pending_license_request.json", {
        "request_token":token, "request_code":req_code, "kind":kind,
        "device_id":device_id(), "business_name":business_name,
        "contact":contact, "created_at":datetime.now(timezone.utc).isoformat()
    })
    return token,result


def poll_online_response(token):
    rows = supa_request("/rest/v1/rpc/get_activation_response", "POST", {"p_request_token": token})
    return rows[0] if rows else None


def save_signed_license(code, payload):
    save_json("license.json", {"code": code, "payload": payload})
    # Cache the cloud registration metadata so device management and sync share one path.
    if isinstance(payload, dict) and payload.get("business_id") and payload.get("sync_token"):
        save_json("cloud_device_registration.json", {
            "business_id": str(payload.get("business_id")),
            "business_name": str(payload.get("business_name") or "My Shop"),
            "sync_token": str(payload.get("sync_token")),
            "device_id": device_id(),
            "expires_at": str(payload.get("expires_at") or ""),
            "device_role": "owner",
            "max_devices": int(payload.get("max_devices") or 1),
            "package_name": str(payload.get("package_name") or "Starter")
        })


def load_saved_license():
    saved = load_json("license.json", None)
    if isinstance(saved, dict) and saved.get("code"):
        return saved
    # Compatibility with the earlier V2 build: old unsigned local JSON must be re-entered once.
    return None

# ---------- Supabase joining-code and device-management RPCs ----------
def _rpc_result(value):
    if isinstance(value, list) and value:
        return value[0]
    return value

def generate_business_join_code(info):
    result = supa_request("/rest/v1/rpc/generate_business_join_code", "POST", {
        "p_business_id": info["business_id"], "p_device_id": info["device_id"],
        "p_sync_token": info["sync_token"], "p_device_name": "Owner device"
    })
    return _rpc_result(result)

def join_business_with_code(code, this_device_id=None):
    result = supa_request("/rest/v1/rpc/join_business_with_code", "POST", {
        "p_join_code": str(code or "").strip(),
        "p_device_id": this_device_id or device_id(),
        "p_device_name": "Shop device"
    })
    result = _rpc_result(result)
    if isinstance(result, dict) and result.get("error"):
        raise RuntimeError(str(result.get("error")))
    if not isinstance(result, dict) or not result.get("business_id") or not result.get("sync_token"):
        raise RuntimeError("Supabase did not return a complete device registration.")
    return result

def list_business_devices(info):
    result = supa_request("/rest/v1/rpc/list_business_devices", "POST", {
        "p_business_id": info["business_id"], "p_device_id": info["device_id"],
        "p_sync_token": info["sync_token"]
    })
    return result if isinstance(result, list) else ([result] if isinstance(result, dict) else [])

def revoke_business_join_code(info):
    return supa_request("/rest/v1/rpc/revoke_business_join_code", "POST", {
        "p_business_id": info["business_id"], "p_device_id": info["device_id"],
        "p_sync_token": info["sync_token"]
    })

def revoke_business_device(info, target_device_id):
    return supa_request("/rest/v1/rpc/revoke_business_device", "POST", {
        "p_business_id": info["business_id"], "p_device_id": info["device_id"],
        "p_sync_token": info["sync_token"], "p_target_device_id": str(target_device_id).strip()
    })

def _error_class(text):
    """Reduce an error message to a short CLASS word. The message itself is never sent."""
    t = str(text or "")
    low = t.lower()
    if not t:
        return ""
    if "network error" in low:
        return "network"
    if "timed out" in low:
        return "timeout"
    m = re.search(r"server http (\d{3})", low)
    if m:
        return "http_" + m.group(1)
    return "other"


def report_device_event(info, event_type, status="", error_class=""):
    """Anonymous device status for Developer Control. Sends ids + a status word only:
    never sales, products, customers, amounts or error text."""
    return supa_request("/rest/v1/rpc/report_device_event", "POST", {
        "p_business_id": info["business_id"], "p_device_id": info["device_id"],
        "p_sync_token": info["sync_token"], "p_event_type": event_type,
        "p_status": status, "p_error_class": error_class, "p_app_version": APP_VERSION
    })


def support_lines(data):
    """Readable lines for the support details the developer published (empty fields skipped)."""
    data = data if isinstance(data, dict) else {}
    rows = []
    for label, key in (("Support", "name"), ("Phone", "phone"), ("WhatsApp", "whatsapp"),
                       ("Email", "email"), ("Website", "website"), ("Hours", "hours")):
        value = str(data.get(key) or "").strip()
        if value:
            rows.append(label + ": " + value)
    message = str(data.get("message") or "").strip()
    if message:
        if rows:
            rows.append("")
        rows.append(message)
    return rows, str(data.get("updated_at") or "").strip()


def support_actions(data):
    """Tap-to-contact actions built from what the developer published: [(label, url)]."""
    data = data if isinstance(data, dict) else {}
    acts = []
    phone = re.sub(r"[^0-9+]", "", str(data.get("phone") or ""))
    if phone:
        acts.append(("Call", "tel:" + phone))
    wa = re.sub(r"\D", "", str(data.get("whatsapp") or ""))
    if wa:
        acts.append(("WhatsApp", "https://wa.me/" + wa))
    email = str(data.get("email") or "").strip()
    if "@" in email:
        acts.append(("Email", "mailto:" + email))
    site = str(data.get("website") or "").strip()
    if site:
        if not re.match(r"^https?://", site, re.I):
            site = "https://" + site
        acts.append(("Website", site))
    return acts


def _cloud_registration():
    value = load_json("cloud_device_registration.json", None)
    return value if isinstance(value, dict) and value.get("business_id") and value.get("sync_token") else None

# ================= LOCAL-FIRST MULTI-DEVICE SYNC =================
# RSA licensing remains unchanged. A device may sync only after its signed
# license contains business_id and sync_token. A single-phone business simply
# has no sync configuration and therefore stays local-only.
SYNC_DATASETS = ("categories", "products", "sales", "expenses", "settings",
                 "purchases", "capital", "weekly_settlements", "monthly_settlements", "ledger")

# What each kind of phone sends / receives. This keeps cloud storage small and keeps history private:
#  - the ADMIN (owner) phone keeps its own sales history, purchases, expenses and accounts on the phone and
#    shares only what employees need to start work (folders, products with prices and stock, settings);
#    it still RECEIVES everything employees send;
#  - EMPLOYEE phones receive only folders / products / settings, and send the work they do (sales,
#    expenses and stock changes) so the admin can read it in the dashboard.
SYNC_LOCAL_ONLY_SETTINGS = ("admin_password",)       # never leaves the phone it was created on
SYNC_POLICY = {
    "owner": {"push": ("categories", "products", "settings"), "pull": SYNC_DATASETS},
    "employee": {"push": ("products", "sales", "expenses"), "pull": ("categories", "products", "settings")},
}
EMPLOYEE_ROLES = ("employee", "cashier", "staff")
SYNC_PUSHED_FILE = "sync_pushed_hashes.json"


def device_role():
    reg = _cloud_registration() or {}
    return str(reg.get("device_role") or "owner").strip().lower()


def device_is_employee():
    return device_role() in EMPLOYEE_ROLES


def sync_policy(role):
    return SYNC_POLICY["employee" if str(role or "").strip().lower() in EMPLOYEE_ROLES else "owner"]


def _remember_device_role(role):
    """The server is the authority on this phone's role; keep the local copy in step with it."""
    reg = load_json("cloud_device_registration.json", None)
    if isinstance(reg, dict) and reg.get("business_id") and str(reg.get("device_role") or "").lower() != role:
        reg["device_role"] = role
        save_json("cloud_device_registration.json", reg)


def _syncable_view(dataset, doc):
    if dataset == "settings" and isinstance(doc, dict):
        return {k: v for k, v in doc.items() if k not in SYNC_LOCAL_ONLY_SETTINGS}
    return dict(doc) if isinstance(doc, dict) else doc


def _plain_sync_error(msg):
    """Short, human reason for a failed sync (the technical text is kept in brackets)."""
    t = str(msg or "").strip()
    low = t.lower()
    if not t:
        return "Tap Sync Now to try again"
    tech = " (" + t.replace("Server HTTP ", "HTTP ")[:70] + ")"
    if "not registered" in low or "unauthor" in low or "http 401" in low or "http 403" in low or "invalid sync" in low:
        return "The cloud did not accept this phone: it is not registered for this business or access was denied. Contact support." + tech
    if "http 404" in low or "could not find the function" in low or "pgrst202" in low:
        return "Cloud sharing is not installed on the server yet. Contact support." + tech
    return "Could not check this business's devices. It will retry automatically." + tech


def _classify_sync_error(msg):
    """Sort a sync error into: offline / not_installed / not_registered / failed."""
    low = str(msg or "").lower()
    if "network error" in low or "timed out" in low:
        return "offline"
    if "http 404" in low or "could not find the function" in low or "pgrst202" in low:
        return "not_installed"        # the server has no device-sharing functions: nothing the shop can fix
    if "not registered" in low or "unauthor" in low or "http 401" in low or "http 403" in low or "invalid sync" in low:
        return "not_registered"
    return "failed"


def _sync_wait_seconds(kind, fails):
    """Seconds before the next AUTOMATIC attempt. Tapping Sync Now always tries immediately."""
    fixed = {"offline": 45, "not_installed": 1800, "not_registered": 600}
    return fixed.get(kind) or min(600, 45 * 2 ** min(max(int(fails), 1) - 1, 4))


def _payload_hash(dataset, payload):
    payload = _syncable_view(dataset, payload)
    return _json_hash(_sync_clean_dict(payload) if isinstance(payload, dict) else payload)


def _record_key(r):
    return str(r.get("dataset")) + ":" + str(r.get("record_id"))


def _unsent_records(records):
    """Only records that are new or changed since they were last sent (not the whole shop every 45 s)."""
    sent = load_json(SYNC_PUSHED_FILE, {})
    sent = sent if isinstance(sent, dict) else {}
    out = []
    for r in records:
        want = "deleted" if r.get("deleted") else _payload_hash(r.get("dataset"), r.get("payload"))
        if sent.get(_record_key(r)) != want:
            out.append(r)
    return out


def _mark_sent(records):
    sent = load_json(SYNC_PUSHED_FILE, {})
    sent = sent if isinstance(sent, dict) else {}
    for r in records:
        sent[_record_key(r)] = "deleted" if r.get("deleted") else _payload_hash(r.get("dataset"), r.get("payload"))
    save_json(SYNC_PUSHED_FILE, sent)


def _sync_license_info():
    cloud = _cloud_registration()
    if cloud:
        return {"business_id": str(cloud.get("business_id") or "").strip(),
                "sync_token": str(cloud.get("sync_token") or "").strip(),
                "device_id": device_id(), "license_code": "cloud-registration"}
    saved = load_saved_license()
    if not isinstance(saved, dict):
        return None
    payload = saved.get("payload") or {}
    if not isinstance(payload, dict):
        return None
    business_id = str(payload.get("business_id") or "").strip()
    sync_token = str(payload.get("sync_token") or "").strip()
    if not business_id or not sync_token:
        return None
    return {"business_id": business_id, "sync_token": sync_token,
            "device_id": device_id(), "license_code": str(saved.get("code") or "")}

def _sync_time():
    return datetime.now(timezone.utc).isoformat()

def _json_hash(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")).hexdigest()

def _sync_clean_dict(item):
    clean = dict(item)
    for key in ("_sync_id", "_sync_hash", "_sync_updated_at", "_sync_device_id"):
        clean.pop(key, None)
    return clean


def _ensure_sync_ids(db, datasets=None):
    """Assign stable IDs to dictionary records without changing legacy string categories."""
    changed = False
    for dataset in (datasets or SYNC_DATASETS):
        value = getattr(db, dataset, None)
        if isinstance(value, list):
            seen = {}
            for item in value:
                if not isinstance(item, dict):
                    continue
                sid = str(item.get("_sync_id") or "").strip()
                if not sid:
                    clean = _sync_clean_dict(item)
                    base = _json_hash(clean)
                    n = seen.get(base, 0)
                    seen[base] = n + 1
                    sid = "legacy-" + base[:24] + ("-" + str(n) if n else "")
                    item["_sync_id"] = sid
                    changed = True
    return changed


def _dataset_records(db, datasets=None):
    """Build stable, timestamped records plus tombstones for locally deleted records."""
    out = []
    live_ids = {}
    known = load_json("sync_known_records.json", {})
    if not isinstance(known, dict):
        known = {}
    deleted_sent = load_json("sync_deleted_sent.json", {})
    if not isinstance(deleted_sent, dict):
        deleted_sent = {}

    for dataset in (datasets or SYNC_DATASETS):
        value = getattr(db, dataset, None)
        current_ids = set()
        if isinstance(value, list):
            seen = {}
            for item in value:
                if isinstance(item, dict):
                    sid = str(item.get("_sync_id") or "").strip()
                    if not sid:
                        continue
                    current_ids.add(sid)
                    clean = _sync_clean_dict(item)
                    h = _json_hash(clean)
                    if str(item.get("_sync_hash") or "") != h:
                        item["_sync_hash"] = h
                        item["_sync_updated_at"] = _sync_time()
                        item["_sync_device_id"] = device_id()
                    out.append({
                        "dataset": dataset, "record_id": sid, "payload": clean,
                        "updated_at": item.get("_sync_updated_at") or _sync_time(),
                        "device_id": item.get("_sync_device_id") or device_id(),
                        "deleted": False
                    })
                else:
                    # Categories are legacy strings. Keep deterministic IDs and timestamps.
                    base = _json_hash([dataset, item])
                    n = seen.get(base, 0)
                    seen[base] = n + 1
                    sid = "value-" + base[:24] + ("-" + str(n) if n else "")
                    current_ids.add(sid)
                    string_state = load_json("sync_string_hashes.json", {})
                    if not isinstance(string_state, dict):
                        string_state = {}
                    key = dataset + ":" + sid
                    payload_hash = _json_hash(item)
                    entry = string_state.get(key, {})
                    if not isinstance(entry, dict) or entry.get("hash") != payload_hash:
                        entry = {"hash": payload_hash, "updated_at": _sync_time()}
                        string_state[key] = entry
                        save_json("sync_string_hashes.json", string_state)
                    out.append({
                        "dataset": dataset, "record_id": sid, "payload": item,
                        "updated_at": entry.get("updated_at") or _sync_time(),
                        "device_id": device_id(), "deleted": False
                    })
        elif isinstance(value, dict):
            current_ids.add("__document__")
            clean = _syncable_view(dataset, value)
            h = _json_hash(clean)
            state = load_json("sync_document_hashes.json", {})
            if not isinstance(state, dict):
                state = {}
            if state.get(dataset) != h:
                state[dataset] = h
                state[dataset + "_updated_at"] = _sync_time()
                save_json("sync_document_hashes.json", state)
            out.append({
                "dataset": dataset, "record_id": "__document__", "payload": clean,
                "updated_at": state.get(dataset + "_updated_at") or _sync_time(),
                "device_id": device_id(), "deleted": False
            })
        live_ids[dataset] = sorted(current_ids)

        previously_known = set(known.get(dataset, [])) if isinstance(known.get(dataset, []), list) else set()
        already_sent = set(deleted_sent.get(dataset, [])) if isinstance(deleted_sent.get(dataset, []), list) else set()
        for sid in sorted(previously_known - current_ids - already_sent):
            out.append({
                "dataset": dataset, "record_id": sid, "payload": {},
                "updated_at": _sync_time(), "device_id": device_id(), "deleted": True
            })

    # Save the proposed live-ID snapshot only after all pushes succeed in sync_now.
    save_json("sync_pending_live_ids.json", live_ids)
    return out


def _sync_headers(info):
    return {"x-device-id": info["device_id"], "x-business-id": info["business_id"],
            "x-sync-token": info["sync_token"]}


def _push_batch(records, info):
    return supa_request("/rest/v1/rpc/sync_push", "POST", {
        "p_business_id": info["business_id"], "p_device_id": info["device_id"],
        "p_sync_token": info["sync_token"], "p_records": records[:SYNC_BATCH_SIZE]
    })


def sync_push_records(records, info):
    if not records:
        return []
    has_ledger = any(r.get("dataset") == "ledger" for r in records)
    try:
        result = _push_batch(records, info)
        if has_ledger:
            save_json("sync_ledger_status.json", {"error": "", "at": _sync_time()})
        return result
    except RuntimeError as err:
        if not has_ledger or "Network error" in str(err) or "timed out" in str(err).lower():
            raise
        # The server may not accept the new "ledger" dataset yet. Keep every other dataset syncing,
        # keep the ledger safely on this phone, and show the problem instead of hiding it.
        others = [r for r in records if r.get("dataset") != "ledger"]
        result = _push_batch(others, info) if others else []
        save_json("sync_ledger_status.json", {"error": str(err)[:300], "at": _sync_time()})
        return result


def run_on_kivy_thread(fn, timeout=60):
    """Run fn() on the Kivy main thread and return its result. The sync worker uses this for EVERY
    change to the shop's records, so the UI and the sync never edit the same lists at the same time."""
    box = {}
    done = threading.Event()

    def run(_dt):
        try:
            box["value"] = fn()
        except Exception as exc:
            box["error"] = exc
        finally:
            done.set()
    Clock.schedule_once(run, 0)
    if not done.wait(timeout):
        raise RuntimeError("Network error: the app was busy, sync will retry")
    if "error" in box:
        raise box["error"]
    return box.get("value")


def sync_pull_records(info):
    state = load_json("sync_state.json", {})
    if not isinstance(state, dict):
        state = {}
    return supa_request("/rest/v1/rpc/sync_pull", "POST", {
        "p_business_id": info["business_id"],
        "p_device_id": info["device_id"],
        "p_sync_token": info["sync_token"],
        "p_since": str(state.get("cursor") or "1970-01-01T00:00:00+00:00"),
        "p_limit": SYNC_BATCH_SIZE,
        "p_after_dataset": str(state.get("after_dataset") or ""),
        "p_after_record_id": str(state.get("after_record_id") or "")
    })


def _replace_or_append(db, dataset, record):
    value = getattr(db, dataset, None)
    sid = str(record.get("record_id") or "")
    payload = record.get("payload")

    if record.get("deleted") is True:
        if isinstance(value, list):
            for i, item in enumerate(value):
                if isinstance(item, dict) and str(item.get("_sync_id") or "") == sid:
                    del value[i]
                    return True
                # Legacy category strings can be removed by their deterministic ID.
                if not isinstance(item, dict):
                    base = _json_hash([dataset, item])
                    if sid.startswith("value-" + base[:24]):
                        del value[i]
                        return True
            return False
        if isinstance(value, dict) and sid == "__document__":
            if value:
                value.clear()
                return True
        return False

    if isinstance(value, list):
        for i, item in enumerate(value):
            if isinstance(item, dict) and str(item.get("_sync_id") or "") == sid:
                incoming_stamp = parse_record_datetime(record.get("updated_at"))
                local_stamp = parse_record_datetime(item.get("_sync_updated_at"))
                if incoming_stamp and local_stamp and incoming_stamp <= local_stamp:
                    return False
                new = dict(payload) if isinstance(payload, dict) else payload
                if isinstance(new, dict):
                    new["_sync_id"] = sid
                    new["_sync_hash"] = _json_hash(_sync_clean_dict(new))
                    new["_sync_updated_at"] = record.get("updated_at") or _sync_time()
                    new["_sync_device_id"] = record.get("device_id") or "remote"
                value[i] = new
                return True
        if isinstance(payload, dict):
            new = dict(payload)
            new["_sync_id"] = sid
            new["_sync_hash"] = _json_hash(_sync_clean_dict(new))
            new["_sync_updated_at"] = record.get("updated_at") or _sync_time()
            new["_sync_device_id"] = record.get("device_id") or "remote"
            value.append(new)
        else:
            if payload in value:
                return False
            value.append(payload)
            string_state = load_json("sync_string_hashes.json", {})
            if not isinstance(string_state, dict):
                string_state = {}
            key = dataset + ":" + sid
            string_state[key] = {
                "hash": _json_hash(payload),
                "updated_at": record.get("updated_at") or _sync_time()
            }
            save_json("sync_string_hashes.json", string_state)
        return True

    if isinstance(value, dict) and sid == "__document__":
        if isinstance(payload, dict):
            state = load_json("sync_document_hashes.json", {})
            if not isinstance(state, dict):
                state = {}
            incoming = _syncable_view(dataset, payload)
            local_view = _syncable_view(dataset, value)
            incoming_stamp = parse_record_datetime(record.get("updated_at"))
            local_stamp = parse_record_datetime(state.get(dataset + "_updated_at"))
            if incoming_stamp and local_stamp and incoming_stamp <= local_stamp and _json_hash(local_view) != _json_hash(incoming):
                return False
            if _json_hash(local_view) == _json_hash(incoming):
                return False
            keep = {k: value[k] for k in SYNC_LOCAL_ONLY_SETTINGS if dataset == "settings" and k in value}
            value.clear()
            value.update(incoming)
            value.update(keep)           # this phone's own admin password is never overwritten
            state[dataset] = _json_hash(_syncable_view(dataset, value))
            state[dataset + "_updated_at"] = record.get("updated_at") or _sync_time()
            save_json("sync_document_hashes.json", state)
            return True
    return False


def merge_remote_records(db, records, allowed=None):
    if not isinstance(records, list):
        raise RuntimeError("Unexpected sync response; expected a list.")
    changed = False
    seen = []
    for record in records:
        if not isinstance(record, dict):
            raise RuntimeError("Invalid sync record from server.")
        dataset = record.get("dataset")
        if dataset not in (allowed or SYNC_DATASETS):
            continue
        changed = _replace_or_append(db, dataset, record) or changed
        seen.append(record)
    if seen:
        _mark_sent(seen)         # what the cloud already holds is not sent back
    if changed:
        db.save_local_only()
    return changed


def money(v):
    try:return f"{float(v):,.2f}"
    except:return "0.00"
from kivy.app import App
from kivy.metrics import dp, sp
from kivy.uix.screenmanager import ScreenManager,Screen,SlideTransition,FadeTransition,NoTransition
from kivy.uix.boxlayout import BoxLayout
from kivy.uix.gridlayout import GridLayout
from kivy.uix.scrollview import ScrollView
from kivy.uix.label import Label
from kivy.uix.button import Button
from kivy.uix.textinput import TextInput
from kivy.uix.spinner import Spinner
from kivy.clock import Clock
from kivy.uix.popup import Popup as _KivyPopup
from kivy.uix.spinner import SpinnerOption
from kivy.uix.behaviors import ButtonBehavior
from kivy.graphics import Color, RoundedRectangle, Line
from kivy.uix.image import Image
from kivy.properties import StringProperty, ObjectProperty

# ---------- App colour palette (premium navy / teal design system) ----------
def hexc(h, a=1.0):
    h = h.lstrip("#")
    return (int(h[0:2], 16) / 255.0, int(h[2:4], 16) / 255.0, int(h[4:6], 16) / 255.0, a)

PRIMARY      = hexc("14243A")   # midnight navy  (title bars, main buttons)
PRIMARY_DARK = hexc("0D1A2B")
PRIMARY_SOFT = hexc("1F3856")
ACCENT       = hexc("20BFA9")   # professional teal (highlights, focus, key actions)
TEAL         = ACCENT
SUCCESS      = hexc("17855A")   # save / confirm
INFO         = hexc("2F6DA3")   # sync / share / navigation
DANGER       = hexc("C8444E")   # delete
PINK         = hexc("4F6D8F")   # legacy name kept; now a muted slate-blue tile colour
SLATE        = hexc("66758C")   # neutral buttons (cancel / close / back)
GREY         = hexc("8793A6")
FOLDER_GOLD  = hexc("E3A93B")
TEXT_DARK    = hexc("14243A")
TEXT_MUTED   = hexc("5E6B7E")
PAGE_BG      = hexc("F5F7FA")   # soft off-white background
CARD_BG      = (1.00, 1.00, 1.00, 1)
CARD_BORDER  = hexc("E1E6EE")
FIELD_BORDER = hexc("C5CFDC")
SELECT_BG    = hexc("DDF5F1")
TILE_COLORS  = [PRIMARY, ACCENT, INFO, PRIMARY_SOFT, SUCCESS, FOLDER_GOLD]
APP_LOGO = "logo_mark"   # key of the embedded logo image (see ICON_DATA)

# ---------- Home dashboard theme (red / black / yellow) ----------
# Only the Home screen is drawn with this palette. The rest of the app keeps the original
# navy / teal design. The swap happens only while Home builds its widgets (see Home.on_pre_enter).
HERO_SUB = (0.80, 0.86, 0.93, 1)
_PALETTE_KEYS = ("PRIMARY", "PRIMARY_DARK", "PRIMARY_SOFT", "ACCENT", "TEAL", "SUCCESS", "INFO", "DANGER",
                 "PINK", "SLATE", "GREY", "FOLDER_GOLD", "TEXT_DARK", "TEXT_MUTED", "PAGE_BG",
                 "CARD_BORDER", "FIELD_BORDER", "SELECT_BG", "TILE_COLORS", "HERO_SUB")
_ORIG_PALETTE = {k: globals()[k] for k in _PALETTE_KEYS}
_HOME_YELLOW, _HOME_RED = hexc("FFC20E"), hexc("D62128")
_HOME_PALETTE = {
    "PRIMARY": hexc("111111"), "PRIMARY_DARK": hexc("000000"), "PRIMARY_SOFT": hexc("2B2B2B"),
    "ACCENT": _HOME_YELLOW, "TEAL": _HOME_YELLOW, "SUCCESS": hexc("B07A00"), "INFO": _HOME_RED,
    "DANGER": hexc("8E0F1B"), "PINK": hexc("9B1C26"), "SLATE": hexc("5C5C5C"), "GREY": hexc("8C8C8C"),
    "FOLDER_GOLD": hexc("F5B800"), "TEXT_DARK": hexc("111111"), "TEXT_MUTED": hexc("666666"),
    "PAGE_BG": hexc("F7F5F0"), "CARD_BORDER": hexc("E6E1D6"), "FIELD_BORDER": hexc("CFC8B8"),
    "SELECT_BG": hexc("FFF1BF"), "HERO_SUB": (0.86, 0.86, 0.86, 1),
}
_HOME_PALETTE["TILE_COLORS"] = [_HOME_PALETTE["PRIMARY"], _HOME_YELLOW, _HOME_RED, _HOME_PALETTE["PRIMARY_SOFT"],
                                _HOME_PALETTE["SUCCESS"], _HOME_PALETTE["FOLDER_GOLD"]]


def _apply_palette(palette):
    globals().update(palette)


# Sync message colours: one distinct colour per state so the user can tell at a glance.
_SYNC_COLORS = {
    "SYNCED":                    (0.08, 0.48, 0.30, 1),   # green  - finished / up to date
    "SYNCING":                   (0.10, 0.30, 0.62, 1),   # blue   - in progress
    "PENDING UPLOAD":            (0.82, 0.55, 0.05, 1),   # amber  - waiting to upload
    "OFFLINE / WAITING TO SYNC": (0.85, 0.35, 0.08, 1),   # orange - offline, will retry
    "SYNC FAILED":               (0.75, 0.18, 0.22, 1),   # red    - failed
    "DEVICE REVOKED":            (0.55, 0.10, 0.15, 1),   # maroon - removed by admin
    "WAITING FOR ADMIN":         (0.45, 0.27, 0.65, 1),   # purple - waiting for admin phone
    "CLOUD NOT CONFIGURED":      (0.62, 0.42, 0.05, 1),   # brown  - setup problem
    "CLOUD NOT SET UP":          (0.45, 0.47, 0.52, 1),   # grey   - works on its own
    "NOT CONNECTED":             (0.62, 0.42, 0.05, 1),   # brown  - not registered
    "LOCAL ONLY":                (0.35, 0.40, 0.48, 1),   # slate  - single phone
}


def sync_status_color(status):
    return _SYNC_COLORS.get(str(status or ""), (0.35, 0.40, 0.48, 1))
MAX_CONTENT_W = dp(720)         # content column is centred on tablets


class Popup(_KivyPopup):
    """Light, readable popup that matches the app colours."""
    def __init__(self, **kwargs):
        kwargs.setdefault("background", "")
        kwargs.setdefault("background_color", (1, 1, 1, 1))
        kwargs.setdefault("overlay_color", (0.08, 0.14, 0.23, 0.55))
        kwargs.setdefault("title_color", PRIMARY)
        kwargs.setdefault("separator_color", ACCENT)
        kwargs.setdefault("separator_height", dp(2))
        kwargs.setdefault("title_size", sp(16))
        super().__init__(**kwargs)


class DB:
    def __init__(self):
        pass

# ============================================================
# SHOP MANAGEMENT SYSTEM
# Licensing / Supabase section below this point is unchanged.
# ============================================================

def normalize_product_name(value):
    """Normalize product names so case, spaces and punctuation do not create duplicates."""
    return re.sub(r"[^a-z0-9]", "", str(value or "").casefold())


def safe_float(value, default=0.0):
    try:
        return float(value)
    except Exception:
        return default


def parse_record_datetime(value):
    try:
        text = str(value or "").strip()
        if not text:
            return None
        if text.endswith("Z"):
            text = text[:-1] + "+00:00"
        return datetime.fromisoformat(text)
    except Exception:
        return None


def record_date(value):
    dt = parse_record_datetime(value)
    return dt.date() if dt else None


def today_date():
    return datetime.now().date()


def money(value):
    d = CURRENCY["decimals"]
    r = round(safe_float(value), d)
    return f"{(0.0 if r == 0 else r):,.{d}f}"


def sale_snapshot(sale):
    """
    Gets the financial values from the moment the sale was made.

    This also supports older sales that don't yet contain the
    new selling_price / gross_profit fields.
    """
    qty = safe_float(sale.get("qty", 0))
    total = safe_float(sale.get("total", 0))
    cost = safe_float(sale.get("cost", 0))

    selling_price = sale.get("selling_price")

    if selling_price is None:
        selling_price = sale.get("sell_price")

    if selling_price is None and qty:
        selling_price = total / qty

    unit_cost = sale.get("unit_cost")

    if unit_cost is None and qty:
        unit_cost = cost / qty

    gross_profit = sale.get("gross_profit")

    if gross_profit is None:
        gross_profit = sale.get("profit")

    if gross_profit is None:
        gross_profit = total - cost

    unit_profit = sale.get("unit_profit")

    if unit_profit is None:
        unit_profit = (
            safe_float(selling_price) -
            safe_float(unit_cost)
        )

    return {
        "qty": qty,
        "total": total,
        "cost": cost,
        "selling_price": safe_float(selling_price),
        "unit_cost": safe_float(unit_cost),
        "unit_profit": safe_float(unit_profit),
        "gross_profit": safe_float(gross_profit),
    }


def period_bounds(kind, value=None):

    from datetime import timedelta

    if kind == "daily":

        if value:
            start = datetime.strptime(
                str(value).strip(),
                "%Y-%m-%d"
            ).date()
        else:
            start = today_date()

        return start, start + timedelta(days=1)

    if kind == "weekly":

        if value:
            d = datetime.strptime(
                str(value).strip(),
                "%Y-%m-%d"
            ).date()
        else:
            d = today_date()

        start = d - timedelta(days=d.weekday())

        return start, start + timedelta(days=7)

    if kind == "monthly":

        if value:
            text = str(value).strip()

            if len(text) == 7:
                d = datetime.strptime(
                    text,
                    "%Y-%m"
                ).date()
            else:
                d = datetime.strptime(
                    text,
                    "%Y-%m-%d"
                ).date()
        else:
            d = today_date()

        start = d.replace(day=1)

        if start.month == 12:
            end = start.replace(
                year=start.year + 1,
                month=1,
                day=1
            )
        else:
            end = start.replace(
                month=start.month + 1,
                day=1
            )

        return start, end

    raise ValueError("Unknown statement period.")


def filter_by_date(records, start, end):
    """Records whose date falls in [start, end), oldest first."""
    out = [r for r in records if (lambda d: d is not None and start <= d < end)(record_date(r.get("date")))]
    out.sort(key=lambda x: parse_record_datetime(x.get("date")) or datetime.min)
    return out


def get_period_records(db, start, end):
    return filter_by_date(db.sales, start, end), filter_by_date(db.expenses, start, end)


def get_period_purchases(db, start, end):
    return filter_by_date(getattr(db, "purchases", []), start, end)


EPOCH_DATE = date(2000, 1, 1)


def calculate_totals(sales, expenses):

    gross_sales = 0.0
    gross_profit = 0.0

    for sale in sales:

        snap = sale_snapshot(sale)

        gross_sales += snap["total"]
        gross_profit += snap["gross_profit"]

    expenses_total = sum(
        safe_float(
            expense.get("amount", 0)
        )
        for expense in expenses
    )

    net_profit = (
        gross_profit -
        expenses_total
    )

    return (
        gross_sales,
        gross_profit,
        expenses_total,
        net_profit
    )


# ===================== FINANCE ENGINE (BEGIN) =====================
# Single source of truth for cash, inventory, debts, profit and capital.
# Every screen (Live Today, statements, Capital, Business Capital dashboard)
# reads from fin_compute(). Nothing here changes existing sales / purchases /
# expenses records; new events are appended to db.ledger (append-only).
import uuid
# ====================================================================================================
# ACCOUNTING ENGINE (BEGIN) - pure-Python double-entry engine, embedded so main.py is a single file.
# Derives every financial field (cost, profit, tax, credit, inventory value, opening worth, depreciation,
# payback) from the shop's own activity and settings. Same code as accounting_engine.py (unit-tested).
# ====================================================================================================
import uuid
from decimal import Decimal, ROUND_HALF_UP, InvalidOperation

from decimal import Decimal, ROUND_HALF_UP, InvalidOperation

# --------------------------------------------------------------------------- money helpers
ZERO = Decimal("0")
CENT = Decimal("0.01")
TOL = Decimal("0.51")           # weighted-average costing leaves sub-unit noise


def D(v):
    """Any value -> Decimal rounded to 0.01. Bad / empty input -> 0 (never raises)."""
    try:
        if v is None or v == "":
            return ZERO
        return Decimal(str(v)).quantize(CENT, ROUND_HALF_UP)
    except (InvalidOperation, ValueError, TypeError):
        return ZERO


def Q(v):
    """Quantity / unit-price: Decimal without rounding."""
    try:
        return Decimal(str(v if v not in (None, "") else 0))
    except (InvalidOperation, ValueError, TypeError):
        return ZERO


def F(v):
    """Decimal -> float for JSON storage / legacy UI."""
    return float(D(v))


def to_dt(value):
    """ISO text -> naive local datetime (timezone-aware values are converted to local time first,
    so a record synced from another phone lands on the same business day everywhere)."""
    try:
        t = str(value or "").strip()
        if not t:
            return None
        if t.endswith("Z"):
            t = t[:-1] + "+00:00"
        dt = datetime.fromisoformat(t)
        if dt.tzinfo is not None:
            dt = dt.astimezone().replace(tzinfo=None)
        return dt
    except Exception:
        return None


def _to_date(value):
    dt = to_dt(value)
    return dt.date() if dt else None


# --------------------------------------------------------------------------- chart of accounts
CASH, AR, INV, EQUIP, OTHER_A = "1000", "1100", "1200", "1500", "1900"
AP, TAXP, OTHER_L = "2000", "2200", "2900"
CAPITAL, DRAWINGS = "3000", "3100"
SALES, SALES_CONTRA, COGS = "4000", "4100", "5000"
OPEX, DEPR, STOCKLOSS, OTHERCOST, TURNTAX = "6000", "6100", "6200", "6300", "6400"
DISPOSAL = "6500"          # loss (or gain, if negative) when old equipment is sold/replaced

ACCOUNTS = {
    CASH: ("Shop cash", "asset"), AR: ("Customers owe us", "asset"), INV: ("Inventory (stock at cost)", "asset"),
    EQUIP: ("Equipment (net)", "asset"), OTHER_A: ("Other assets", "asset"),
    AP: ("We owe suppliers", "liability"), TAXP: ("Tax payable", "liability"),
    OTHER_L: ("Other liabilities", "liability"),
    CAPITAL: ("Owner capital", "equity"), DRAWINGS: ("Owner drawings", "equity"),
    SALES: ("Sales", "income"), SALES_CONTRA: ("Sales returns & discounts", "income"),
    COGS: ("Cost of goods sold", "expense"), OPEX: ("Operating expenses", "expense"),
    DEPR: ("Depreciation", "expense"), STOCKLOSS: ("Stock losses & adjustments", "expense"),
    OTHERCOST: ("Other business costs", "expense"), TURNTAX: ("Turnover tax", "expense"),
    DISPOSAL: ("Loss / (gain) on equipment replaced", "expense"),
}
OPENING_MAP = {            # opening_balance ledger account -> (journal account, sign)
    "cash": (CASH, 1), "inventory": (INV, 1), "equipment": (EQUIP, 1), "other_assets": (OTHER_A, 1),
    "receivables": (AR, 1), "payables": (AP, -1), "other_liabilities": (OTHER_L, -1),
}
UNNAMED_CUSTOMER = "(walk-in / unnamed)"
UNNAMED_SUPPLIER = "(unnamed supplier)"
OPENING_PARTY = "(opening balance)"

DEFAULT_EXPENSE_RULES = {
    "Rent": ["rent", "lease", "premises"],
    "Salaries & wages": ["salary", "salaries", "wage", "wages", "payroll", "worker", "attendant"],
    "Utilities": ["electric", "power", "umeme", "water", "yaka", "utility", "utilities", "gas"],
    "Transport": ["transport", "fuel", "boda", "taxi", "delivery", "fare", "petrol", "diesel", "freight"],
    "Communication": ["airtime", "data bundle", "internet", "wifi", "phone", "sms"],
    "Licences & taxes": ["licence", "license", "permit", "tax", "levy", "ura", "council", "kcca"],
    "Repairs & maintenance": ["repair", "maintenance", "fix", "service fee", "plumber", "electrician"],
    "Packaging & supplies": ["packag", "bag", "polythene", "paper roll", "receipt roll", "cleaning", "soap"],
    "Marketing": ["advert", "marketing", "promo", "poster", "flyer", "sign board", "signboard"],
    "Security": ["security", "guard", "alarm"],
    "Bank & mobile money charges": ["bank charge", "withdraw fee", "momo", "mobile money", "airtel money", "commission"],
}


def auto_category(description, rules=None):
    """Expense category from the description - no manual category field."""
    text = " " + str(description or "").casefold() + " "
    for cat, words in (rules or DEFAULT_EXPENSE_RULES).items():
        if any(str(w).casefold() in text for w in words):
            return cat
    return "Other expenses"


# --------------------------------------------------------------------------- set-up
class Setup(object):
    TAX_MODES = ("none", "vat", "turnover")

    def __init__(self, settings=None):
        s = settings if isinstance(settings, dict) else {}
        self.currency = (str(s.get("currency_code") or "UGX").strip().upper()[:6]) or "UGX"
        try:
            self.decimals = max(0, min(3, int(s.get("currency_decimals", 0))))
        except Exception:
            self.decimals = 0
        mode = str(s.get("tax_mode") or "none").strip().lower()
        self.tax_mode = mode if mode in self.TAX_MODES else "none"
        self.tax_rate = max(ZERO, D(s.get("tax_rate", 0)))
        if self.tax_rate <= 0:
            self.tax_mode = "none"
        self.prices_include_tax = bool(s.get("prices_include_tax", True))
        self.tax_start = _to_date(s.get("tax_effective_date"))
        self.auto_fund = bool(s.get("auto_fund_shortfall", True))
        try:
            self.fy_month = max(1, min(12, int(s.get("fiscal_year_start_month", 1))))
        except Exception:
            self.fy_month = 1
        try:
            self.equipment_life = max(0.25, float(s.get("equipment_life_years", 5)))
        except Exception:
            self.equipment_life = 5.0
        self.auto_depreciation = bool(s.get("auto_depreciation", True))
        rules = dict(DEFAULT_EXPENSE_RULES)
        extra = s.get("expense_rules")
        if isinstance(extra, dict):
            for k, v in extra.items():
                if isinstance(v, (list, tuple)):
                    rules[str(k)] = [str(x) for x in v]
        self.expense_rules = rules

    def fmt(self, v):
        d = self.decimals
        r = round(float(v), d)
        r = 0.0 if r == 0 else r
        return ("-" if r < 0 else "") + self.currency + " " + f"{abs(r):,.{d}f}"

    def vat_in(self, gross, when):
        """VAT contained in a tax-inclusive amount."""
        if self.tax_mode != "vat":
            return ZERO
        if self.tax_start and when and when.date() < self.tax_start:
            return ZERO
        return (gross * self.tax_rate / (100 + self.tax_rate)).quantize(CENT, ROUND_HALF_UP)

    def turnover_tax(self, gross, when):
        if self.tax_mode != "turnover":
            return ZERO
        if self.tax_start and when and when.date() < self.tax_start:
            return ZERO
        return (gross * self.tax_rate / 100).quantize(CENT, ROUND_HALF_UP)

    def fiscal_year_bounds(self, on=None):
        on = on or date.today()
        y = on.year if on.month >= self.fy_month else on.year - 1
        start = date(y, self.fy_month, 1)
        return start, date(y + 1, self.fy_month, 1)


# --------------------------------------------------------------------------- journal
def L(acct, amount, tag="", party=""):
    return (acct, D(amount), tag, party)


def live_ledger(rows):
    """Ledger records that count in the books. A reversed transaction and its reversal entry are BOTH left
    out, so the books look exactly as if the transaction had never been recorded (the journal still lists
    both, for the audit trail)."""
    rows = [e for e in (rows or []) if isinstance(e, dict)]
    gone = {e.get("reversal_of") for e in rows if e.get("reversal_of")}
    return [e for e in rows if not e.get("reversal_of") and not e.get("reversed_by")
            and e.get("txn_id") not in gone]


class Entry(object):
    __slots__ = ("when", "kind", "ref", "memo", "lines", "cf", "auto")

    def __init__(self, when, kind, ref, memo, lines, cf="operating", auto=False):
        self.when, self.kind, self.ref, self.memo = when, kind, ref, memo
        self.lines, self.cf, self.auto = lines, cf, auto

    @property
    def cash(self):
        return sum((l[1] for l in self.lines if l[0] == CASH), ZERO)


class Books(object):
    """Derived, balanced, deterministic books. Build once, read as many statements as needed.
    Two phones with the same records always produce identical books."""

    def __init__(self, db):
        self.db = db
        self.setup = Setup(getattr(db, "settings", None))
        self.entries = []
        self.problems = []        # records that could not be posted (reported by checks())
        self.bad_dates = []
        self._cash = ZERO
        self._open_amt, self._open_date = {}, {}
        self._first = None
        self.assets = []          # depreciable assets: (cost, start_date, life_years)
        self._build()

    # ---- building -------------------------------------------------------------------------
    def _append(self, e):
        self.entries.append(e)
        self._cash += e.cash

    def _add(self, when, kind, ref, memo, lines, cf="operating", allow_fund=True):
        lines = [l for l in lines if l[1] != ZERO]
        if not lines:
            return
        if sum((l[1] for l in lines), ZERO) != ZERO:
            self.problems.append((kind, ref, "unbalanced entry skipped"))
            return
        cash = sum((l[1] for l in lines if l[0] == CASH), ZERO)
        if allow_fund and self.setup.auto_fund and self._cash + cash < ZERO:
            need = -(self._cash + cash)      # the owner must have put this money in
            self._append(Entry(when, "auto_funding", ref, "Owner money added automatically to cover: " + str(memo),
                               [L(CASH, need), L(CAPITAL, -need, "auto")], "financing", True))
        self._append(Entry(when, kind, ref, memo, lines, cf))

    def _build(self):
        db, ev = self.db, []

        def take(rows, prio, kind):
            for i, r in enumerate(rows or []):
                if not isinstance(r, dict):
                    continue
                w = to_dt(r.get("date"))
                if w is None:
                    self.bad_dates.append((kind, r))
                    continue
                ev.append((w, prio, i, kind, r))

        take(getattr(db, "purchases", []), 0, "purchase")
        take(getattr(db, "sales", []), 1, "sale")
        take(getattr(db, "expenses", []), 2, "expense")
        take((getattr(db, "capital", None) or {}).get("transactions", []), 3, "legacy_owner")
        take([e for e in live_ledger(getattr(db, "ledger", []))
              if e.get("type") not in ("opening_balance", "fund_transfer")], 4, "ledger")
        self._opening()
        ev.sort(key=lambda x: (x[0], x[1], x[2]))
        self._first = ev[0][0].date() if ev else None
        self._collect_assets()
        for when, _, _, kind, r in ev:
            try:
                getattr(self, "_post_" + kind)(when, r)
            except Exception as exc:                      # one bad record must not stop the books
                self.problems.append((kind, str(r.get("receipt_no") or r.get("txn_id") or r.get("date")), str(exc)))

    def _collect_assets(self):
        """Equipment list (cost, bought, life, name, id). Replacements retire an old item and add the new one.
        Used by the REPLACEMENT PLAN; the cash/capital effect of a replacement is posted in _post_ledger."""
        st, led = self.setup, live_ledger(getattr(self.db, "ledger", []))
        life = Decimal(str(st.equipment_life))
        eq = self._open_amt.get("equipment", ZERO)
        if eq > 0:
            starts = [d for d in (self._open_date.get("equipment"), self._first) if d]
            if starts:
                self.assets.append((eq, min(starts), life, "Equipment owned at the start", "opening"))
        for e in led:
            if e.get("type") == "equipment_purchase":
                d, c = _to_date(e.get("date")), D(e.get("amount"))
                if d and c > 0:
                    try:
                        yrs = Decimal(str(float(e.get("life_years") or st.equipment_life)))
                    except Exception:
                        yrs = life
                    name = str(e.get("note") or "").strip() or "Equipment"
                    self.assets.append((c, d, max(yrs, Decimal("0.25")), name, str(e.get("txn_id") or "")))
        for e in sorted([x for x in led if x.get("type") == "equipment_replacement"], key=lambda x: str(x.get("date"))):
            oc, ref, d = D(e.get("old_cost")), e.get("old_ref"), _to_date(e.get("date"))
            for i, a in enumerate(self.assets):
                if a[4] == ref:
                    if a[0] - oc > CENT / 2:
                        self.assets[i] = (a[0] - oc,) + tuple(a[1:])
                    else:
                        del self.assets[i]
                    break
            nc = D(e.get("amount"))
            if d and nc > 0:
                try:
                    yrs = Decimal(str(float(e.get("life_years") or st.equipment_life)))
                except Exception:
                    yrs = life
                self.assets.append((nc, d, max(yrs, Decimal("0.25")), str(e.get("note") or "").strip() or "Equipment",
                                    str(e.get("txn_id") or "")))

    def replacement_plan(self, as_of=None):
        """Plain-language saving plan for replacing equipment. Pure estimate: no money moves."""
        today = as_of or date.today()
        rows, daily_total, should_total, cost_total = [], ZERO, ZERO, ZERO
        for cost, start, life, name, aid in self.assets:
            life_days = Decimal("365.25") * life
            days = max(0, (today - start).days)
            used = min(cost, cost * Decimal(days) / life_days)          # part of the cost "used up" so far
            worn_out = Decimal(days) >= life_days
            per_day = (cost / life_days).quantize(Decimal("1"), ROUND_HALF_UP)
            per_day = max(per_day, Decimal("1")) if cost > 0 else ZERO
            replace_on = start + timedelta(days=int(life_days))
            rows.append({"id": aid, "name": name, "cost": F(cost), "bought": start, "life_years": float(life),
                         "replace_on": replace_on, "per_day": F(per_day), "worn_out": worn_out,
                         "days_left": (replace_on - today).days,
                         "used_up": F(used), "value_now": F(cost - used), "should_have": F(used)})
            should_total += used
            cost_total += cost
            if not worn_out:
                daily_total += per_day
        rows.sort(key=lambda r: r["replace_on"])
        return {"as_of": today, "assets": rows, "per_day_total": F(daily_total),
                "should_have_total": F(should_total), "cost_total": F(cost_total)}

    def _depr_upto(self, upto):
        if upto is None:
            return ZERO
        total = ZERO
        for cost, start, life, _name, _aid in self.assets:
            days = max(0, (upto - start).days)
            total += min(cost, cost * Decimal(days) / (Decimal("365.25") * life))
        return total.quantize(CENT, ROUND_HALF_UP)

    def _auto_depr(self, start, end):
        return self._depr_upto(end) - self._depr_upto(start) if self.assets else ZERO

    def _opening(self):
        best = {}
        for idx, e in enumerate(getattr(self.db, "ledger", []) or []):
            if isinstance(e, dict) and e.get("type") == "opening_balance" and e.get("account") in OPENING_MAP:
                stamp = (str(e.get("date") or ""), idx)
                if e["account"] not in best or stamp >= best[e["account"]][0]:
                    best[e["account"]] = (stamp, D(e.get("amount")))
        lines = []
        for acc, (stamp, amt) in best.items():
            self._open_amt[acc], self._open_date[acc] = amt, _to_date(stamp[0])
            jacct, sign = OPENING_MAP[acc]
            party = OPENING_PARTY if jacct in (AR, AP) else ""
            lines.append(L(jacct, sign * amt, "", party))
        if lines:
            # Opening owner's equity is the balancing figure of the opening position (assets - liabilities).
            lines.append(L(CAPITAL, -sum((l[1] for l in lines), ZERO), "opening"))
            self._append(Entry(datetime.min, "opening", "opening", "Opening position", lines, "opening"))

    # ---- posting rules (one per kind of record) -------------------------------------------
    def _post_sale(self, when, s):
        st = self.setup
        total = D(s.get("total"))
        qty = Q(s.get("qty"))
        cost = D(s.get("cost")) if s.get("cost") is not None else (qty * Q(s.get("unit_cost"))).quantize(CENT)
        paid = s.get("amount_paid")
        paid = total if paid is None else min(max(D(paid), ZERO), total)     # legacy sales: paid in full
        credit = total - paid
        vat = D(s.get("tax_amount")) if s.get("tax_amount") is not None else st.vat_in(total, when)
        who = str(s.get("customer_name") or "").strip() or UNNAMED_CUSTOMER
        ref = str(s.get("receipt_no") or "")
        lines = [L(CASH, paid), L(AR, credit, "", who), L(SALES, -(total - vat), str(s.get("income_category") or "Sales")),
                 L(TAXP, -vat, "vat"), L(COGS, cost), L(INV, -cost)]
        t = st.turnover_tax(total, when)
        lines += [L(TURNTAX, t), L(TAXP, -t, "turnover")]
        self._add(when, "sale", ref, "Sale %s #%s" % (s.get("product", ""), ref), lines)

    def _post_purchase(self, when, p):
        total = D(p.get("total_cost"))
        paid = p.get("paid_amount")
        paid = total if paid is None else min(max(D(paid), ZERO), total)     # legacy purchases: paid in cash
        credit = total - paid
        who = str(p.get("supplier") or "").strip() or UNNAMED_SUPPLIER
        if p.get("opening_stock") is True:
            # Stock the shop already owned when it started using the app: part of the STARTING WORTH.
            # No cash moves; the paid part is owner's equity, any unpaid part is owed to the supplier.
            self._add(when, "opening_stock", str(p.get("pid") or ""), "Opening stock: %s" % p.get("product", ""),
                      [L(INV, total), L(AP, -credit, "", who), L(CAPITAL, -paid, "opening")], "opening", False)
            return
        self._add(when, "purchase", str(p.get("pid") or ""), "Stock bought: %s" % p.get("product", ""),
                  [L(INV, total), L(CASH, -paid), L(AP, -credit, "", who)])

    def _post_expense(self, when, x):
        cat = str(x.get("category") or "") or auto_category(x.get("description"), self.setup.expense_rules)
        a = D(x.get("amount"))
        self._add(when, "expense", str(x.get("txn_id") or ""), "Expense: %s" % x.get("description", ""),
                  [L(OPEX, a, cat), L(CASH, -a)])

    def _post_legacy_owner(self, when, tx):
        a = D(tx.get("amount"))
        if tx.get("type") == "withdrawal":
            self._add(when, "owner_withdrawal", "", "Owner withdrawal", [L(DRAWINGS, a), L(CASH, -a)], "financing", False)
        else:
            self._add(when, "owner_investment", "", "Owner investment", [L(CASH, a), L(CAPITAL, -a, "invest")], "financing")

    def _post_ledger(self, when, e):
        t, a, ref = e.get("type"), D(e.get("amount")), str(e.get("txn_id") or "")
        party = str(e.get("party") or "").strip()
        rev = bool(e.get("reversal_of"))
        label = str(t).replace("_", " ").capitalize() + ((": " + party) if party else "")
        add = lambda lines, cf="operating", fund=True: self._add(when, t, ref, label, lines, cf, fund and not rev)
        if t == "owner_investment":
            add([L(CASH, a), L(CAPITAL, -a, "invest")], "financing")
        elif t == "owner_withdrawal":
            add([L(DRAWINGS, a), L(CASH, -a)], "financing", False)
        elif t == "supplier_payment":
            add([L(AP, a, "", party or UNNAMED_SUPPLIER), L(CASH, -a)])
        elif t == "customer_payment":
            add([L(CASH, a), L(AR, -a, "", party or UNNAMED_CUSTOMER)])
        elif t == "tax_payment":
            add([L(TAXP, a), L(CASH, -a)])
        elif t == "equipment_purchase":
            add([L(EQUIP, a), L(CASH, -a)], "investing")
        elif t == "equipment_replacement":
            # old item sold for `proceeds`; its book cost leaves Equipment; the difference is the loss (or gain);
            # the new item is bought at `amount`. Cash moves only by (proceeds - new cost).
            pr, oc = D(e.get("proceeds")), D(e.get("old_cost"))
            add([L(CASH, pr), L(EQUIP, -oc), L(DISPOSAL, oc - pr), L(EQUIP, a), L(CASH, -a)], "investing")
        elif t == "depreciation":
            add([L(DEPR, a), L(EQUIP, -a)])
        elif t == "other_cost":
            add([L(OTHERCOST, a), L(CASH, -a)])
        elif t == "stock_writeoff":
            c = D(e.get("cost", e.get("amount")))
            add([L(STOCKLOSS, c, "writeoff"), L(INV, -c)])
        elif t == "inventory_adjustment":
            add([L(INV, a), L(STOCKLOSS, -a, "adjustment")])
        elif t == "debt_forward":
            who = party or (UNNAMED_CUSTOMER if e.get("kind") == "customer" else UNNAMED_SUPPLIER)
            if e.get("kind") == "customer":
                add([L(AR, a, "", who), L(CAPITAL, -a, "opening")])
            else:
                add([L(CAPITAL, a, "opening"), L(AP, -a, "", who)])
        elif t in ("sales_return", "sales_discount"):
            tag = "return" if t == "sales_return" else "discount"
            vat = self.setup.vat_in(a, when)
            tt = self.setup.turnover_tax(a, when)
            lines = [L(SALES_CONTRA, a - vat, tag), L(TAXP, vat, "vat"), L(TAXP, tt, "turnover"), L(TURNTAX, -tt)]
            if e.get("settles", "paid") == "receivable":
                lines.append(L(AR, -a, "", party or UNNAMED_CUSTOMER))
            else:
                lines.append(L(CASH, -a))
            c = D(e.get("cost"))
            if t == "sales_return" and e.get("restock") and c != ZERO:
                lines += [L(INV, c), L(COGS, -c)]
            add(lines)
        else:
            self.problems.append(("ledger", ref, "unknown type " + str(t)))

    # ---- aggregation ---------------------------------------------------------------------
    def _agg(self, start=None, end=None, kinds=None):
        acct, tags = {}, {}
        for e in self.entries:
            d = e.when.date()
            if (start and d < start) or (end and d >= end) or (kinds and e.kind not in kinds):
                continue
            for a, amt, tg, _ in e.lines:
                acct[a] = acct.get(a, ZERO) + amt
                tags[(a, tg)] = tags.get((a, tg), ZERO) + amt
        # Equipment is NOT written down automatically any more. Business Capital shows the real figure;
        # wear on equipment lives only in the Equipment Replacement Plan (see replacement_plan()).
        return acct, tags

    @staticmethod
    def _end(end):
        return end if end is not None else date.today() + timedelta(days=1)

    # ---- statements ----------------------------------------------------------------------
    def income_statement(self, start=None, end=None):
        a, t = self._agg(start, self._end(end))
        g = lambda k: a.get(k, ZERO)
        gross = -g(SALES)
        returns, disc = t.get((SALES_CONTRA, "return"), ZERO), t.get((SALES_CONTRA, "discount"), ZERO)
        net_sales = gross - returns - disc
        cogs = g(COGS)
        gp = net_sales - cogs
        opex = g(OPEX)
        other = {"Stock write-offs": t.get((STOCKLOSS, "writeoff"), ZERO),
                 "Inventory cost adjustments": t.get((STOCKLOSS, "adjustment"), ZERO),
                 "Depreciation": g(DEPR), "Loss / (gain) on equipment replaced": g(DISPOSAL),
                 "Other costs / taxes": g(OTHERCOST) + g(TURNTAX)}
        other_total = sum(other.values(), ZERO)
        net = gp - opex - other_total
        by_cat = {}
        for (acc, tag), v in t.items():
            if acc == OPEX and v != ZERO:
                by_cat[tag or "Other expenses"] = by_cat.get(tag or "Other expenses", ZERO) + v
        fixed, ratio = opex + other_total, (gp / net_sales if net_sales > 0 else ZERO)
        return {"gross_sales": gross, "returns": returns, "discounts": disc, "net_sales": net_sales,
                "cogs": cogs, "gross_profit": gp, "operating_profit": gp - opex,
                "depreciation": other["Depreciation"], "cash_profit": net + other["Depreciation"] + other["Loss / (gain) on equipment replaced"],
                "gross_margin_pct": float(gp / net_sales * 100) if net_sales > 0 else None,
                "operating_expenses": opex, "expense_by_category": by_cat,
                "other_breakdown": other, "other_costs": other_total, "net_profit": net,
                "break_even_sales": (fixed / ratio) if ratio > 0 else None,
                "tax_collected_vat": -t.get((TAXP, "vat"), ZERO)}

    def balance_sheet(self, end=None):
        end = self._end(end)
        a, _ = self._agg(None, end)
        g = lambda k: a.get(k, ZERO)
        assets = {k: g(k) for k in (CASH, AR, INV, EQUIP, OTHER_A)}
        liab = {k: -g(k) for k in (AP, TAXP, OTHER_L)}
        retained = -sum((v for k, v in a.items() if ACCOUNTS[k][1] in ("income", "expense")), ZERO)
        capital, drawings = -g(CAPITAL), g(DRAWINGS)
        # TODAY's position uses the stock really on the shelves (quantity x cost), so every screen shows the
        # same inventory figure. The book figure (purchases - cost of sales) can drift, even below zero, when
        # stock was added or edited without a purchase record. The difference is shown as a "stock difference"
        # inside owner's equity; it is never slipped into profit.
        inv_book, stock_gap = assets[INV], ZERO
        if end > date.today():
            stock_gap = self.physical_inventory() - inv_book
            assets[INV] = inv_book + stock_gap
        total_a, total_l = sum(assets.values(), ZERO), sum(liab.values(), ZERO)
        equity = capital - drawings + retained + stock_gap
        cur_a = assets[CASH] + assets[AR] + assets[INV]
        return {"assets": assets, "liabilities": liab, "total_assets": total_a, "total_liabilities": total_l,
                "owner_capital": capital, "owner_drawings": drawings, "retained_profit": retained,
                "inventory_book": inv_book, "stock_difference": stock_gap,
                "total_equity": equity, "balanced": abs(total_a - total_l - equity) < CENT,
                "working_capital": cur_a - total_l, "net_capital": total_a - total_l,
                "current_ratio": float(cur_a / total_l) if total_l > 0 else None}

    def trial_balance(self, end=None):
        a, _ = self._agg(None, self._end(end))
        rows = [(k, ACCOUNTS[k][0], v if v > 0 else ZERO, -v if v < 0 else ZERO) for k, v in sorted(a.items()) if v != ZERO]
        return rows, sum(r[2] for r in rows), sum(r[3] for r in rows)

    def cash_flow(self, start=None, end=None):
        end = self._end(end)
        opening = ZERO
        flows = {"operating": {}, "investing": {}, "financing": {}}
        for e in self.entries:
            d, c = e.when.date(), e.cash
            if c == ZERO:
                continue
            if e.cf == "opening" or (start and d < start):
                opening += c
                continue
            if d >= end:
                continue
            bucket = flows.get(e.cf, flows["operating"])
            bucket[e.kind] = bucket.get(e.kind, ZERO) + c
        totals = {k: sum(v.values(), ZERO) for k, v in flows.items()}
        return {"opening_cash": opening, "flows": flows, "totals": totals,
                "net_change": sum(totals.values(), ZERO), "closing_cash": opening + sum(totals.values(), ZERO)}

    def parties(self, kind, end=None):
        acct = AR if kind == "customer" else AP
        sign = 1 if kind == "customer" else -1
        out = {}
        for e in self.entries:
            if e.when.date() >= self._end(end):
                continue
            for a, amt, _, party in e.lines:
                if a == acct:
                    out[party or "(unnamed)"] = out.get(party or "(unnamed)", ZERO) + sign * amt
        return {k: v for k, v in out.items() if abs(v) >= Decimal("0.005")}

    def owner_totals(self, start=None, end=None):
        a, t = self._agg(start, self._end(end), kinds=("owner_investment", "owner_withdrawal", "auto_funding", "legacy_owner"))
        return -a.get(CAPITAL, ZERO), a.get(DRAWINGS, ZERO)

    def auto_fundings(self):
        """Every time the shop's cash was too small for a payment and the engine recorded the missing money
        as put in by the owner. The owner is asked to remark where that money came from."""
        out = []
        for e in self.entries:
            if e.auto and e.kind == "auto_funding":
                amt = -sum((l[1] for l in e.lines if l[0] == CAPITAL), ZERO)
                out.append({"key": e.when.isoformat() + "|" + str(e.ref) + "|" + str(amt), "when": e.when,
                            "amount": F(amt), "for": str(e.memo).split("cover: ", 1)[-1]})
        return out

    def owner_funded_automatically(self):
        return sum((-l[1] for e in self.entries if e.auto for l in e.lines if l[0] == CAPITAL), ZERO)

    # ---- starting worth (what the business was worth when the customer began using the app) ----
    def opening_position(self):
        keys = ("opening", "opening_stock")
        acc = {}
        for e in self.entries:
            if e.kind in keys + ("debt_forward",):
                for a, amt, _, _ in e.lines:
                    acc[a] = acc.get(a, ZERO) + amt
        eq = -sum((l[1] for e in self.entries if e.kind in keys + ("debt_forward",) for l in e.lines if l[0] == CAPITAL), ZERO)
        starts = [e.when.date() for e in self.entries if e.when != datetime.min and not e.auto]
        starts += [d for d in self._open_date.values() if d]
        stock = [p for p in getattr(self.db, "purchases", []) or [] if isinstance(p, dict) and p.get("opening_stock") is True]
        return {"inventory": acc.get(INV, ZERO), "cash": acc.get(CASH, ZERO), "receivables": acc.get(AR, ZERO),
                "payables": -acc.get(AP, ZERO), "equipment": acc.get(EQUIP, ZERO),
                "other_assets": acc.get(OTHER_A, ZERO), "other_liabilities": -acc.get(OTHER_L, ZERO),
                "worth": eq, "started_on": min(starts) if starts else None, "opening_stock_lines": len(stock)}

    # ---- investment, return and payback ------------------------------------------------------------
    def investment_report(self, end=None):
        """How much was put into the business, what it has earned, and how much has been recovered."""
        end = self._end(end)
        op = self.opening_position()
        life = self.income_statement(None, end)
        bs = self.balance_sheet(end)
        inj, wd = self.owner_totals(None, end)
        invested = op["worth"] + inj
        net, dep = life["net_profit"], life["depreciation"]
        cash_profit = net + dep                      # depreciation is a cost on paper, not cash going out
        started = op["started_on"]
        days = max(1, (end - started).days) if started else 0
        months = max(Decimal(days) / Decimal("30.4375"), Decimal(1)) if days else ZERO
        avg_cash = cash_profit / months if months else ZERO
        roi = net / invested * 100 if invested > 0 else None
        left = invested - cash_profit
        if invested <= 0:
            months_left = None
        elif left <= 0:
            months_left = Decimal(0)
        else:
            months_left = left / avg_cash if avg_cash > 0 else None
        return {"starting_worth": op["worth"], "opening": op, "owner_investments": inj,
                "auto_funded": self.owner_funded_automatically(), "total_invested": invested,
                "owner_drawings": wd, "accounting_profit": net, "operating_profit": life["operating_profit"],
                "depreciation": dep, "cash_profit": cash_profit,
                "roi_pct": float(roi) if roi is not None else None,
                "roi_yearly_pace_pct": float(roi * 365 / days) if roi is not None and days >= 30 else None,
                "recovered": cash_profit, "still_to_recover": max(ZERO, left),
                "payback_pct": float(cash_profit / invested * 100) if invested > 0 else None,
                "payback_months_left": float(months_left) if months_left is not None else None,
                "avg_monthly_cash_profit": avg_cash, "profit_kept": net - wd,
                "worth_now": bs["net_capital"], "growth_since_start": bs["net_capital"] - op["worth"],
                "started_on": started, "days_active": days,
                "reconciles": abs(bs["net_capital"] - (invested - wd + net)) <= TOL}

    def monthly_profit(self, end=None, months=6):
        end = self._end(end)
        y, m = (end - timedelta(days=1)).year, (end - timedelta(days=1)).month
        spans = []
        for _ in range(months):
            spans.append((date(y, m, 1), date(y + (m == 12), m % 12 + 1, 1)))
            y, m = (y, m - 1) if m > 1 else (y - 1, 12)
        out, began = [], self.opening_position()["started_on"]
        for a, b in reversed(spans):
            if began is None or b <= began:          # nothing to show before the shop started using the app
                continue
            p = self.income_statement(a, min(b, end))
            out.append({"month": a.strftime("%Y-%m"), "net_sales": p["net_sales"], "gross_profit": p["gross_profit"],
                        "accounting_profit": p["net_profit"]})
        return out

    # ---- drill-down rows used by the detail screens ------------------------------------------
    def cash_movements(self, end=None):
        end, rows = self._end(end), []
        for e in self.entries:
            if e.when.date() < end and e.cash != ZERO:
                rows.append({"date": None if e.when == datetime.min else e.when.isoformat(), "account": "cash",
                             "amount": float(e.cash), "kind": e.kind, "desc": e.memo})
        return rows

    def party_rows(self, kind, end=None):
        end, acct, sign, rows = self._end(end), (AR if kind == "customer" else AP), (1 if kind == "customer" else -1), []
        for e in self.entries:
            if e.when.date() < end:
                for a, amt, _, party in e.lines:
                    if a == acct:
                        rows.append((None if e.when == datetime.min else e.when.isoformat(), party or "(unnamed)", float(sign * amt), e.memo))
        return rows

    # ---- inventory truth ----------------------------------------------------------------
    def physical_inventory(self):
        prods = sum(max(ZERO, Q(p.get("qty"))) * max(ZERO, Q(p.get("buy"))) for p in getattr(self.db, "products", []) or [])
        svc = sum(max(ZERO, D(t.get("remaining_cost"))) for t in (getattr(self.db, "settings", {}) or {}).get("service_stock_transfers", []))
        return D(prods) + svc

    def inventory_true_up(self):
        """Proposed adjustment (amount, note) when shelves differ from the books. The app posts it
        through its normal ledger; the engine never changes profit silently."""
        diff = self.physical_inventory() - self.balance_sheet()["inventory_book"]
        if abs(diff) <= TOL:
            return None
        return {"type": "inventory_adjustment", "amount": F(diff),
                "note": "Stock valuation true-up (shelf value %s vs books)" % self.setup.fmt(self.physical_inventory())}

    # ---- integrity checks -------------------------------------------------------------------
    def checks(self, end=None):
        end = self._end(end)
        bs = self.balance_sheet(end)
        out = []

        def chk(name, expected, actual, note=""):
            out.append({"name": name, "expected": float(expected), "actual": float(actual),
                        "ok": abs(Decimal(str(expected)) - Decimal(str(actual))) <= TOL, "note": note})

        chk("Every journal entry balances (skipped records)", 0, len(self.problems),
            "; ".join("%s %s: %s" % p for p in self.problems[:3]))
        chk("Assets = liabilities + owner's equity", bs["total_assets"], bs["total_liabilities"] + bs["total_equity"])
        a, _ = self._agg(None, end)
        chk("Shop cash is never negative", max(ZERO, a.get(CASH, ZERO)), a.get(CASH, ZERO),
            "Negative cash means a withdrawal exceeded cash (auto-funding never covers withdrawals).")
        chk("Customer balances add up to receivables", sum(self.parties("customer", end).values(), ZERO), a.get(AR, ZERO))
        chk("Supplier balances add up to payables", sum(self.parties("supplier", end).values(), ZERO), -a.get(AP, ZERO))
        if end > date.today():
            chk("Inventory on shelves = inventory in books", bs["inventory_book"], self.physical_inventory(),
                "A difference means stock or cost was edited outside a purchase/sale. See inventory_true_up().")
        chk("Records with unreadable dates (excluded)", 0, len(self.bad_dates))
        chk("Products with negative stock", 0, len([p for p in getattr(self.db, "products", []) or [] if Q(p.get("qty")) < 0]))
        chk("Customers with a credit (overpaid) balance", 0, len([v for v in self.parties("customer", end).values() if v < 0]))
        return out

    # ---- legacy-shaped output (drop-in for fin_compute / fin_pnl users) -----------------------
    def legacy_pnl(self, start=None, end=None):
        end = self._end(end)
        p = self.income_statement(start, end)
        sales = [s for s in getattr(self.db, "sales", []) or [] if isinstance(s, dict)
                 and (lambda d: d is not None and (start is None or d >= start) and d < end)(_to_date(s.get("date")))]
        agg = lambda kind, acct, want_pos: sum((l[1] for e in self.entries if e.kind == kind and (start is None or e.when.date() >= start)
                                                and e.when.date() < end for l in e.lines if l[0] == acct and (l[1] > 0) == want_pos), ZERO)
        bought = agg("purchase", INV, True)
        paid = -agg("purchase", CASH, False)
        inj, wd = self.owner_totals(start, end)
        return {"gross_sales": F(p["gross_sales"]), "discounts": F(p["discounts"]), "returns": F(p["returns"]),
                "net_sales": F(p["net_sales"]), "cogs": F(p["cogs"]), "gross_profit": F(p["gross_profit"]),
                "gross_margin_pct": p["gross_margin_pct"], "operating_expenses": F(p["operating_expenses"]),
                "other_costs": F(p["other_costs"]), "other_breakdown": {k: F(v) for k, v in p["other_breakdown"].items()},
                "net_profit": F(p["net_profit"]), "units": sum(float(Q(s.get("qty"))) for s in sales),
                "cash_from_sales": F(agg("sale", CASH, True)), "collections": F(agg("customer_payment", CASH, True)),
                "debts_paid": F(-agg("supplier_payment", CASH, False)),
                "stock_purchased": F(bought), "stock_purchased_paid": F(paid), "stock_purchased_credit": F(bought - paid),
                "owner_investments": F(inj), "owner_withdrawals": F(wd),
                "break_even_sales": F(p["break_even_sales"]) if p["break_even_sales"] is not None else None}

    def legacy_compute(self, start=None, end=None):
        end = self._end(end)
        bs = self.balance_sheet(end)
        A, Lb = bs["assets"], bs["liabilities"]
        phys = self.physical_inventory()
        opening_eq = -sum((l[1] for e in self.entries if e.kind in ("opening", "opening_stock", "debt_forward") and e.when.date() < end
                           for l in e.lines if l[0] == CAPITAL), ZERO)
        pos = {"inventory": F(A[INV]), "inventory_book": F(bs["inventory_book"]), "inventory_physical": F(phys),
               "stock_difference": F(bs["stock_difference"]),
               "cash": F(A[CASH]), "bank": 0.0, "mobile_money": 0.0, "cash_total": F(A[CASH]),
               "receivables": F(A[AR]), "payables": F(Lb[AP]), "loans_short": 0.0, "loans_long": 0.0, "loans": 0.0,
               "equipment": F(A[EQUIP]), "other_assets": F(A[OTHER_A]), "other_liabilities": F(Lb[OTHER_L] + Lb[TAXP]),
               "total_assets": F(bs["total_assets"]), "total_liabilities": F(bs["total_liabilities"]),
               "net_capital": F(bs["net_capital"]), "current_assets": F(A[CASH] + A[AR] + A[INV]),
               "current_liabilities": F(bs["total_liabilities"]), "working_capital": F(bs["working_capital"]),
               "opening_equity": F(opening_eq), "ending_equity": F(bs["total_equity"]),
               "equity_difference": F(bs["net_capital"] - bs["total_equity"])}
        return {"start": start, "end": end, "setup_done": bool(self.entries), "period": self.legacy_pnl(start, end),
                "lifetime": self.legacy_pnl(None, end),
                "customers": {k: F(v) for k, v in self.parties("customer", end).items()},
                "suppliers": {k: F(v) for k, v in self.parties("supplier", end).items()}, "position": pos}


# --------------------------------------------------------------------------- convenience API
def books(db):
    return Books(db)


def fin_compute(db, start=None, end=None):
    c = Books(db).legacy_compute(start, end)
    try:
        # sales are limited to the statement period; stock figures are as at the period's end
        _end = c.get("end") if isinstance(c.get("end"), date) else None
        _start = c.get("start") if isinstance(c.get("start"), date) else None
        _pool = None
        if _start is not None and _end is not None:
            _pool = [x for x in (getattr(db, "sales", []) or [])
                     if (record_date(x.get("date")) is not None and _start <= record_date(x.get("date")) < _end)]
        c["service_recovery"] = service_recovery_summary(db, _pool, as_of=_end)
    except Exception:
        c["service_recovery"] = None
    return c


def fin_pnl(db, start=None, end=None):
    return Books(db).legacy_pnl(start, end)


# --------------------------------------------------------------------------- equipment replacement plan
# A saving PLAN only. Nothing here touches cash, capital, profit or the ledger. The owner notes down money
# they really set aside; it is kept in settings (so it syncs) under "replacement_savings".
def replacement_savings(db):
    rows = db.settings.get("replacement_savings") if isinstance(getattr(db, "settings", None), dict) else None
    return [r for r in (rows or []) if isinstance(r, dict) and safe_float(r.get("amount")) > 0]


def replacement_add_saving(db, amount, note="", key=None):
    amount = safe_float(amount)
    if amount <= 0:
        raise ValueError("Type how much you put aside.")
    rows = list(replacement_savings(db))
    sid = str(key or "S-" + uuid.uuid4().hex[:12])
    if any(r.get("id") == sid for r in rows):          # double tap: already saved
        return
    rows.append({"id": sid, "date": datetime.now().isoformat(timespec="seconds"),
                 "amount": round(amount, 2), "note": str(note or "").strip()})
    db.settings["replacement_savings"] = rows


def replacement_undo_last(db):
    rows = list(replacement_savings(db))
    if not rows:
        return None
    last = rows.pop()
    db.settings["replacement_savings"] = rows
    return last


FUNDING_SOURCES = ("My own money", "Money from family or a friend", "Sales money I forgot to record", "A loan", "Other")
_FUNDING_SNOOZED = set()          # asked "later" during this session


def fin_funding_pending(db):
    done = db.settings.get("funding_remarks") if isinstance(db.settings, dict) else None
    done = done if isinstance(done, dict) else {}
    return [f for f in Books(db).auto_fundings() if f["key"] not in done]


def fin_prompt_funding_remark(screen, *_):
    """If the shop recorded money as 'put in by the owner' automatically, ask where it came from."""
    try:
        db = screen.manager.app.db
        todo = [f for f in fin_funding_pending(db) if f["key"] not in _FUNDING_SNOOZED]
    except Exception:
        return
    if not todo:
        return
    f = todo[0]
    box = BoxLayout(orientation="vertical", padding=dp(10), spacing=dp(6))
    txt = AppLabel(text="The shop did not have enough cash for: " + f["for"] + ".\n"
                        + fin_fmt(f["amount"]) + " was recorded as money you put in. Where did this money come from?",
                   font_size=sp(12), halign="left", valign="middle", size_hint_y=None, height=dp(96))
    txt.bind(width=lambda i, w: setattr(i, "text_size", (w, None)))
    src = AppSpinner(text=FUNDING_SOURCES[0], values=FUNDING_SOURCES, size_hint_y=None, height=dp(44))
    remark = AppTextInput(hint_text="Remark (optional)", multiline=False, size_hint_y=None, height=dp(44))
    save = AppButton(text="SAVE REMARK", background_color=SUCCESS, size_hint_y=None, height=dp(46))
    later = AppButton(text="LATER", background_color=GREY, size_hint_y=None, height=dp(42))
    for w in (txt, src, remark, save, later):
        box.add_widget(w)
    popup = Popup(title="Money added to the business", content=box, size_hint=(.94, .7), auto_dismiss=False)

    def do_save(*_):
        marks = db.settings.get("funding_remarks")
        marks = dict(marks) if isinstance(marks, dict) else {}
        marks[f["key"]] = {"source": src.text, "remark": remark.text.strip(),
                           "saved": datetime.now().isoformat(timespec="seconds")}
        db.settings["funding_remarks"] = marks
        db.save()
        popup.dismiss()
        if hasattr(screen, "on_pre_enter"):
            screen.on_pre_enter()
        Clock.schedule_once(lambda dt: fin_prompt_funding_remark(screen), 0.3)

    def do_later(*_):
        _FUNDING_SNOOZED.add(f["key"])
        popup.dismiss()
    save.bind(on_release=do_save)
    later.bind(on_release=do_later)
    popup.open()


def fin_replacement(db, as_of=None):
    """Plan + what the owner has noted as put aside. as_of defaults to today."""
    plan = Books(db).replacement_plan(as_of)
    saved = sum(safe_float(r.get("amount")) for r in replacement_savings(db))
    plan["saved_total"] = round(saved, 2)
    plan["gap"] = round(plan["should_have_total"] - saved, 2)       # >0 means still short
    # Money already put aside reduces the "value left" shown for each item (shared by its daily share).
    weights = [max(safe_float(r.get("per_day")), 0.0) for r in plan["assets"]]
    if sum(weights) <= 0:
        weights = [max(safe_float(r.get("cost")), 0.0) for r in plan["assets"]]
    wsum = sum(weights)
    for r, w in zip(plan["assets"], weights):
        share = saved * w / wsum if wsum > 0 else 0.0
        r["value_now"] = round(max(0.0, safe_float(r.get("cost")) - share), 2)
    return plan


def fin_party_balances(db, kind, end=None):
    return {k: F(v) for k, v in Books(db).parties(kind, end).items()}


def fin_reconcile(db, end=None):
    return Books(db).checks(end)


def fin_cash_movements(db, end=None):
    return Books(db).cash_movements(end)


def fin_party_rows(db, kind, end=None):
    return Books(db).party_rows(kind, end)


def fin_owner_totals(db, start=None, end=None):
    i, w = Books(db).owner_totals(start, end)
    return float(i), float(w)


def fin_physical_inventory(db):
    return float(Books(db).physical_inventory())


def fin_book_inventory(db, end=None):
    return float(Books(db).balance_sheet(end)["assets"][INV])


def fin_setup_done(db):
    return bool(Books(db).entries)


def starting_worth(db):
    """What the business was worth when the customer started using the app (opening stock + opening
    cash/debts, all captured automatically). Returned as floats for the UI."""
    o = Books(db).opening_position()
    return {k: (F(v) if isinstance(v, Decimal) else v) for k, v in o.items()}


def fin_investment(db, end=None, months=6):
    """Investment / return / payback figures as plain floats for the UI."""
    b = Books(db)
    r = b.investment_report(end)

    def fl(v):
        if isinstance(v, Decimal):
            return F(v)
        if isinstance(v, dict):
            return {k: fl(x) for k, x in v.items()}
        return v
    out = {k: fl(v) for k, v in r.items()}
    out["months"] = [{k: (F(v) if isinstance(v, Decimal) else v) for k, v in m.items()} for m in b.monthly_profit(end, months)]
    return out


def period_snapshot(db, start, end, books=None):
    """What a weekly / monthly settlement should store - position AS OF the period end
    (the old settlement stored today's stock value against a past date)."""
    b = books or Books(db)
    p, bs = b.income_statement(start, end), b.balance_sheet(end)
    return {"period_start": start.isoformat(), "period_end": (end - timedelta(days=1)).isoformat(),
            "settled_at": datetime.now().isoformat(), "gross_sale": F(p["gross_sales"]), "gross_profit": F(p["gross_profit"]),
            "expenses": F(p["operating_expenses"] + p["other_costs"]), "net_profit": F(p["net_profit"]),
            "capital_end": F(bs["net_capital"]), "capital_inventory": F(bs["assets"][INV]),
            "capital_cash": F(bs["assets"][CASH]), "receivables_end": F(bs["assets"][AR]),
            "payables_end": F(bs["liabilities"][AP])}


# --------------------------------------------------------------------------- automatic capture
def _stamp(now=None):
    return (now or datetime.now()).isoformat()


def capture_sale(db, cart, cash_received=None, customer="", now=None, device_tag=""):
    """cart = [{"product": <product dict>, "qty": n, "price": unit_price}, ...]
    Returns the sale records, each with EVERY financial field filled in. Stock is reduced here.
    The caller only calls db.save() afterwards. cash_received=None means 'paid in full'."""
    st = Setup(getattr(db, "settings", None))
    if not cart:
        raise ValueError("Cart is empty.")
    now = now or datetime.now()
    lines, need = [], {}
    for x in cart:
        pid = str((x["product"] or {}).get("pid", "") or "")
        live = next((p for p in db.products if pid and str(p.get("pid", "")) == pid), x["product"])
        qty, price = Q(x.get("qty")), Q(x.get("price"))
        if qty <= 0 or price < 0:
            raise ValueError("Quantity must be above zero and price cannot be negative.")
        need[id(live)] = need.get(id(live), ZERO) + qty
        if need[id(live)] > Q(live.get("qty")) + Decimal("0.000001"):
            raise ValueError("Not enough stock for %s: available %g" % (live.get("name", ""), float(Q(live.get("qty")))))
        net = (qty * price).quantize(CENT, ROUND_HALF_UP)
        if st.tax_mode == "vat" and not st.prices_include_tax:
            vat = (net * st.tax_rate / 100).quantize(CENT, ROUND_HALF_UP)
            total = net + vat
        else:
            total = net
            vat = st.vat_in(total, now)
        cost = (qty * Q(live.get("buy"))).quantize(CENT, ROUND_HALF_UP)
        lines.append((live, qty, total, vat, cost))
    grand = sum((l[2] for l in lines), ZERO)
    cash = grand if cash_received in (None, "") else D(cash_received)
    if cash < 0:
        raise ValueError("Cash received cannot be negative.")
    customer = str(customer or "").strip()
    if grand - cash > Decimal("0.004") and not customer:
        raise ValueError("Cash is short by %s. Enter the customer's name to record the balance as credit." % st.fmt(grand - cash))
    base = now.strftime("%Y%m%d%H%M%S") + (("-" + device_tag) if device_tag else "")
    used = {str(s.get("receipt_no")) for s in db.sales[-500:]}
    receipt, n = base, 2
    while receipt in used:
        receipt, n = "%s-%d" % (base, n), n + 1
    left, saved = min(cash, grand), []
    for live, qty, total, vat, cost in lines:
        got = min(total, left)
        left -= got
        live["qty"] = float(Q(live.get("qty")) - qty)
        unit_price = (total / qty).quantize(Decimal("0.0001")) if qty else ZERO
        unit_cost = (cost / qty).quantize(Decimal("0.0001")) if qty else ZERO
        profit = total - vat - cost
        rec = {"date": _stamp(now), "txn_id": "S-" + uuid.uuid4().hex[:16].upper(), "product": live.get("name", ""),
               "product_pid": live.get("pid", ""), "unit": live.get("unit", "Piece"), "qty": float(qty),
               "selling_price": float(unit_price), "sell_price": float(unit_price), "unit_cost": float(unit_cost),
               "unit_profit": float(unit_price - unit_cost), "total": F(total), "tax_amount": F(vat),
               "cost": F(cost), "gross_profit": F(profit), "profit": F(profit), "receipt_no": receipt,
               "customer_name": customer, "cash_paid": F(cash), "change_given": F(max(ZERO, cash - grand)),
               "amount_paid": F(got), "credit_amount": F(total - got), "method": "cash", "sale_type": "stock",
               "income_category": "Sales"}
        db.sales.append(rec)
        saved.append(rec)
    return saved


def is_opening_stock(db, product):
    """Opening stock = a product's FIRST stock, entered before the first sale. It is what the shop
    already owned when it started using the app, so it counts towards the starting worth."""
    pid = product.get("pid")
    return (not db.sales and Q(product.get("qty")) <= 0
            and not any(isinstance(p, dict) and pid and p.get("product_pid") == pid for p in db.purchases))


def capture_purchase(db, product, qty, total_cost, supplier="", paid_amount=None, now=None, category=None, opening=None):
    """Restock (or first stock of a new product shell with qty 0). Updates weighted-average cost and
    writes the purchase record with paid/credit/status filled. paid_amount=None means paid in full."""
    qty, total = Q(qty), D(total_cost)
    if qty <= 0 or total < 0:
        raise ValueError("Quantity must be above zero and cost cannot be negative.")
    paid = total if paid_amount in (None, "") else D(paid_amount)
    if paid < 0 or paid > total:
        raise ValueError("Amount paid now must be between 0 and the total cost.")
    supplier = str(supplier or "").strip()
    if total - paid > Decimal("0.004") and not supplier:
        raise ValueError("Enter the supplier's name when stock is bought on credit.")
    if not product.get("pid"):
        product["pid"] = "P-" + uuid.uuid4().hex[:16]
    opening = is_opening_stock(db, product) if opening is None else bool(opening)
    old_q, old_c = max(ZERO, Q(product.get("qty"))), max(ZERO, Q(product.get("buy")))
    new_q = old_q + qty
    product["buy"] = float(((old_q * old_c + total) / new_q).quantize(Decimal("0.0001")))
    product["qty"] = float(new_q)
    rec = {"date": _stamp(now), "pid": "B-" + uuid.uuid4().hex[:16], "product": product.get("name", ""),
           "product_pid": product["pid"], "qty": float(qty), "unit": product.get("unit", "Piece"),
           "unit_cost": float((total / qty).quantize(Decimal("0.0001"))), "total_cost": F(total),
           "category": category or product.get("category", "Other"), "supplier": supplier, "paid_amount": F(paid),
           "method": "cash", "opening_stock": opening, "status": "paid" if total - paid < Decimal("0.005") else ("unpaid" if paid < Decimal("0.005") else "part-paid")}
    db.purchases.append(rec)
    return rec


def capture_expense(db, description, amount, now=None, category=None):
    """Expense with automatic category. Paid from shop cash; owner funding is derived if cash is short."""
    name, a = str(description or "").strip(), D(amount)
    if not name:
        raise ValueError("Expense description is required.")
    if a <= 0:
        raise ValueError("Expense amount must be greater than zero.")
    st = Setup(getattr(db, "settings", None))
    rec = {"date": _stamp(now), "txn_id": "E-" + uuid.uuid4().hex[:16].upper(), "description": name, "amount": F(a),
           "category": category or auto_category(name, st.expense_rules), "method": "cash"}
    db.expenses.append(rec)
    return rec
# ACCOUNTING ENGINE (END) ==============================================================================

CURRENCY = {"code": "UGX", "decimals": 0}
CASH_ACCOUNTS = ("cash",)
ACCOUNT_LABELS = {"cash": "Shop cash"}
OPENING_ACCOUNTS = ("equity", "cash", "inventory", "equipment", "receivables",
                    "payables", "other_assets", "other_liabilities")
FIN_TYPES = ("opening_balance", "owner_investment", "owner_withdrawal",
             "supplier_payment", "customer_payment", "equipment_purchase",
             "depreciation", "stock_writeoff", "inventory_adjustment", "sales_discount",
             "sales_return", "fund_transfer", "other_cost", "debt_forward", "equipment_replacement")
FIN_TYPE_LABELS = {
    "opening_balance": "Opening balance", "owner_investment": "Owner investment",
    "owner_withdrawal": "Owner withdrawal", "supplier_payment": "Supplier payment",
    "customer_payment": "Customer payment", "equipment_purchase": "Equipment purchase",
    "equipment_replacement": "Equipment replaced / upgraded",
    "depreciation": "Depreciation", "stock_writeoff": "Stock write-off",
    "inventory_adjustment": "Inventory cost adjustment", "sales_discount": "Sales discount",
    "sales_return": "Sales return",
    "other_cost": "Other business cost", "debt_forward": "Debt brought forward"}
UNNAMED_CUSTOMER = "(walk-in / unnamed)"
UNNAMED_SUPPLIER = "(unnamed supplier)"
OPENING_PARTY = "(opening balance)"
FIN_TOLERANCE = 0.51   # weighted-average costing leaves sub-shilling noise


def fin_r2(v):
    return round(safe_float(v), 2)


def fin_apply_settings(db):
    s = getattr(db, "settings", {}) or {}
    code = str(s.get("currency_code") or "UGX").strip().upper()[:6] or "UGX"
    try:
        dec = int(s.get("currency_decimals", 0))
    except Exception:
        dec = 0
    CURRENCY["code"] = code
    CURRENCY["decimals"] = max(0, min(3, dec))


def fin_fmt(v, code=True):
    """UGX 1,234,567 (no decimals by default). Negative values show a leading minus."""
    d = CURRENCY["decimals"]
    r = round(safe_float(v), d)
    if r == 0:
        r = 0.0
    text = f"{abs(r):,.{d}f}"
    if r < 0:
        text = "-" + text
    return (CURRENCY["code"] + " " + text) if code else text


def fin_ensure(db):
    """Idempotent upgrade: adds db.ledger and stable product ids. Never removes data."""
    changed = False
    if not isinstance(getattr(db, "ledger", None), list):
        db.ledger = []
        changed = True
    for p in db.products:
        if isinstance(p, dict) and not p.get("pid"):
            key = [normalize_product_name(p.get("name", "")), normalize_product_name(p.get("brand", "")),
                   normalize_product_name(p.get("variant", "")), normalize_product_name(p.get("product_class", ""))]
            p["pid"] = "P-" + _json_hash(key)[:16]   # deterministic: same product -> same id on every device
            changed = True
    return changed


def fin_find_product(db, pid="", name=""):
    if pid:
        for p in db.products:
            if p.get("pid") == pid:
                return p
    if name:
        n = normalize_product_name(name)
        found = [p for p in db.products if normalize_product_name(p.get("name", "")) == n]
        if len(found) == 1:
            return found[0]
    return None


def _in_range(value, start, end):
    d = record_date(value)
    if d is None:
        return False
    return (start is None or d >= start) and (end is None or d < end)


def _acct(rec):
    m = str(rec.get("method") or "cash")
    return m if m in CASH_ACCOUNTS else "cash"


def _ledger(db, *types):
    return [e for e in getattr(db, "ledger", []) if isinstance(e, dict) and e.get("type") in types]


def _sale_paid(sale):
    snap = sale_snapshot(sale)
    paid = sale.get("amount_paid")
    paid = snap["total"] if paid is None else safe_float(paid)   # legacy sales were paid in full
    return paid, snap["total"] - paid


def _purchase_paid(pu):
    total = safe_float(pu.get("total_cost"))
    paid = pu.get("paid_amount")
    paid = total if paid is None else safe_float(paid)           # legacy purchases were paid in cash
    return paid, total - paid


# ------------------------------------------------------------------ posting
def _fin_validate_and_apply(db, e):
    t = e["type"]
    rev = bool(e.get("reversal_of"))
    a = safe_float(e.get("amount"))
    pos = lambda v, msg: (_ for _ in ()).throw(ValueError(msg)) if (not rev and v <= 0) else None
    if t in ("sales_discount", "sales_return"):
        e.setdefault("settles", "paid")
        if e["settles"] not in ("paid", "receivable"):
            raise ValueError("Settlement must be 'paid' or 'receivable'.")
    needs_method = t not in ("opening_balance", "stock_writeoff", "inventory_adjustment", "depreciation", "debt_forward") and \
        not (t in ("sales_discount", "sales_return") and e.get("settles") == "receivable")
    if needs_method:
        e["method"] = e.get("method") or "cash"
        if e["method"] not in CASH_ACCOUNTS:
            raise ValueError("Shop transactions use shop cash only.")
    else:
        e["method"] = "none"
    if t == "equipment_replacement":
        if rev:
            return
        proceeds = safe_float(e.get("proceeds"))
        if a <= 0:
            raise ValueError("Type the cost of the new equipment.")
        if proceeds < 0:
            raise ValueError("The price the old equipment sold for cannot be negative.")
        asset = next((x for x in Books(db).replacement_plan()["assets"] if x["id"] == e.get("old_ref")), None)
        if asset is None:
            raise ValueError("Choose the equipment you are replacing.")
        oc = safe_float(e.get("old_cost")) or asset["cost"]
        if oc <= 0 or oc > asset["cost"] + 0.005:
            raise ValueError("The old cost cannot be more than " + fin_fmt(asset["cost"]) + ".")
        e["old_cost"], e["proceeds"], e["old_name"] = fin_r2(oc), fin_r2(proceeds), asset["name"]
        return
    if t == "opening_balance":
        if e.get("account") not in OPENING_ACCOUNTS or a < 0:
            raise ValueError("Opening balance needs a valid account and a non-negative amount.")
        return
    if t == "debt_forward":
        # A named debt that already existed (or arose outside this app). No cash moves and no profit
        # is made; opening capital moves by the same amount (see fin_compute) so the books stay balanced.
        if not rev:
            if e.get("kind") not in ("customer", "supplier"):
                raise ValueError("Choose customer or supplier.")
            if not str(e.get("party") or "").strip():
                raise ValueError("Enter the " + str(e.get("kind")) + "'s name.")
            if a <= 0:
                raise ValueError("Amount must be greater than zero.")
        elif e.get("kind") in ("customer", "supplier"):
            who = str(e.get("party") or "").strip() or (UNNAMED_CUSTOMER if e["kind"] == "customer" else UNNAMED_SUPPLIER)
            if fin_party_balances(db, e["kind"]).get(who, 0.0) + a < -0.005:
                raise ValueError("Payments were already recorded against this debt. Reverse those payments first.")
        return
    if t == "inventory_adjustment":
        if not rev and (abs(a) < 0.005 or not str(e.get("note") or "").strip()):
            raise ValueError("An inventory adjustment needs a non-zero amount and a reason.")
        return
    if t in ("owner_investment", "owner_withdrawal", "equipment_purchase", "other_cost",
             "supplier_payment", "customer_payment", "sales_discount", "fund_transfer", "depreciation"):
        pos(a, "Amount must be greater than zero.")
    if t == "owner_withdrawal" and not rev:
        available = fin_compute(db)["position"].get(e.get("method"), 0.0)
        if a > available + 0.005:
            raise ValueError(f"{ACCOUNT_LABELS.get(e.get('method'), 'Selected account')} has only {fin_fmt(max(available, 0))}. Withdrawal exceeds available funds.")
    if t == "supplier_payment" and not rev:
        have_cash = fin_compute(db)["position"]["cash"]
        if a > have_cash + 0.005:
            raise ValueError(f"Shop cash has only {fin_fmt(max(have_cash, 0))}. A supplier payment comes out of shop cash; "
                             "record the owner's money first if it was paid from outside the shop.")
    if t in ("supplier_payment", "customer_payment") and not rev:
        party = str(e.get("party") or "").strip()
        if not party:
            raise ValueError("Choose the " + ("supplier" if t == "supplier_payment" else "customer") + ".")
        bal = fin_party_balances(db, "supplier" if t == "supplier_payment" else "customer").get(party, 0.0)
        if a > bal + 0.005:
            raise ValueError(f"{party} only has {fin_fmt(max(bal,0))} outstanding. Overpayments are not recorded.")
    if t == "depreciation" and not rev and a > fin_compute(db)["position"]["equipment"] + 0.005:
        raise ValueError("Depreciation is more than the recorded equipment value.")
    if t == "fund_transfer":
        if e.get("to_method") not in CASH_ACCOUNTS or e["to_method"] == e["method"]:
            raise ValueError("Choose two different accounts for a transfer.")
        if not rev:
            have = fin_compute(db)["position"][e["method"]]
            if a > have + 0.005:
                raise ValueError(f"{ACCOUNT_LABELS[e['method']]} only has {fin_fmt(have)}.")
    if t in ("stock_writeoff", "sales_return"):
        qty = safe_float(e.get("qty"))
        if not rev and qty <= 0:
            raise ValueError("Quantity must be greater than zero.")
        p = fin_find_product(db, e.get("product_pid", ""), e.get("product", ""))
        if t == "stock_writeoff":
            if p is None:
                raise ValueError("Product not found.")
            if not rev:
                if qty > safe_float(p.get("qty")) + 1e-9:
                    raise ValueError(f"Only {safe_float(p.get('qty')):g} in stock.")
                e["cost"] = fin_r2(qty * safe_float(p.get("buy")))
                e["amount"] = e["cost"]
            p["qty"] = safe_float(p.get("qty")) - qty
            e["product_pid"], e["product"] = p.get("pid", ""), p.get("name", "")
        else:
            pos(a, "Refund / revenue reversed must be greater than zero.")
            e["restock"] = bool(e.get("restock"))
            if e["restock"]:
                if p is None:
                    raise ValueError("Product not found, so it cannot be put back into stock.")
                if not rev:
                    unit = safe_float(e.get("unit_cost")) if e.get("unit_cost") not in (None, "") else safe_float(p.get("buy"))
                    e["cost"] = fin_r2(qty * unit)
                newq = safe_float(p.get("qty")) + qty
                if newq < -1e-9:
                    raise ValueError("That would make stock negative.")
                p["qty"] = newq
                e["product_pid"], e["product"] = p.get("pid", ""), p.get("name", "")
            else:
                e["cost"] = 0.0


def fin_post(db, entry, dedupe_key=None):
    """Append one financial event. Returns (entry, created). A repeated dedupe_key or txn_id
    returns the original entry and created=False, so retries and syncs never double-post."""
    fin_ensure(db)
    e = dict(entry)
    if e.get("type") not in FIN_TYPES:
        raise ValueError("Unknown financial transaction type.")
    key = dedupe_key or e.get("dedupe_key")
    for old in db.ledger:
        if (key and old.get("dedupe_key") == key) or (e.get("txn_id") and old.get("txn_id") == e["txn_id"]):
            return old, False
    if key:
        e["dedupe_key"] = key
    for k in ("amount", "principal", "interest", "cost", "proceeds", "old_cost"):
        if k in e:
            e[k] = fin_r2(e[k])
    if "qty" in e:
        e["qty"] = round(safe_float(e["qty"]), 4)
    e.setdefault("date", datetime.now().isoformat())
    e.setdefault("status", "posted")
    e["txn_id"] = e.get("txn_id") or "T-" + uuid.uuid4().hex[:20].upper()
    e["_sync_id"] = e["txn_id"]
    _fin_validate_and_apply(db, e)
    db.ledger.append(e)
    return e, True


def fin_reverse(db, txn_id, reason=""):
    """Correct a mistake by posting an equal-and-opposite entry. History is never edited or deleted."""
    orig = next((x for x in db.ledger if x.get("txn_id") == txn_id), None)
    if orig is None:
        raise ValueError("Transaction not found.")
    if orig.get("type") == "opening_balance":
        raise ValueError("Opening balances are corrected by entering a new opening balance.")
    if orig.get("reversal_of"):
        raise ValueError("A reversal cannot itself be reversed; post the transaction again instead.")
    if orig.get("reversed_by"):
        raise ValueError("This transaction has already been reversed.")
    # Items recorded together (e.g. equipment brought in by the owner = owner money + equipment) go together.
    bundle = orig.get("bundle")
    if bundle:
        for sib in [x for x in db.ledger if x.get("bundle") == bundle and x.get("txn_id") != txn_id
                    and not x.get("reversed_by") and not x.get("reversal_of")]:
            fin_reverse(db, sib["txn_id"], reason)
    if orig.get("type") in ("equipment_purchase", "equipment_replacement"):
        for x in live_ledger(db.ledger):
            if x.get("type") == "equipment_replacement" and x.get("old_ref") == txn_id:
                raise ValueError("This equipment was replaced later. Reverse that replacement first.")
    rev = dict(orig)
    for k in ("txn_id", "_sync_id", "dedupe_key", "reversed_by", "_sync_hash", "_sync_updated_at", "_sync_device_id"):
        rev.pop(k, None)
    for k in ("amount", "principal", "interest", "cost", "qty", "proceeds", "old_cost"):
        if k in rev:
            rev[k] = -safe_float(rev[k])
    rev["reversal_of"] = txn_id
    rev["date"] = datetime.now().isoformat()
    rev["note"] = ("Reversal: " + reason).strip() if reason else "Reversal of " + txn_id
    saved, created = fin_post(db, rev, dedupe_key="reverse:" + txn_id)
    if created:
        orig["reversed_by"] = saved["txn_id"]
    return saved


# ------------------------------------------------------------------ drill-down & reconciliation
def fin_detail(db, key, start=None, end=None):
    """(title, rows[(date, description, amount)]) behind one dashboard figure."""
    rows = []
    title = key
    if key == "sales":
        title = "Gross sales"
        rows = [(s.get("date"), f"{s.get('product','')} x{safe_float(s.get('qty')):g} #{s.get('receipt_no','')}",
                 sale_snapshot(s)["total"] - safe_float(s.get("tax_amount"))) for s in db.sales if _in_range(s.get("date"), start, end)]
    elif key == "cogs":
        title = "Cost of goods sold (recorded cost of units sold)"
        rows = [(s.get("date"), f"{s.get('product','')} x{safe_float(s.get('qty')):g}", sale_snapshot(s)["cost"])
                for s in db.sales if _in_range(s.get("date"), start, end)]
    elif key == "expenses":
        title = "Operating expenses"
        rows = [(x.get("date"), str(x.get("description", "")), safe_float(x.get("amount")))
                for x in db.expenses if _in_range(x.get("date"), start, end)]
    elif key == "purchases":
        title = "Stock purchases (paid + credit)"
        rows = [(p.get("date"), f"{p.get('product','')} x{safe_float(p.get('qty')):g}"
                 + (" [credit: " + fin_fmt(_purchase_paid(p)[1], False) + "]" if _purchase_paid(p)[1] > 0.004 else ""),
                 safe_float(p.get("total_cost"))) for p in db.purchases if _in_range(p.get("date"), start, end)]
    elif key in ("discounts", "returns", "other_costs", "owner"):
        types = {"discounts": ("sales_discount",), "returns": ("sales_return",),
                 "other_costs": ("stock_writeoff", "inventory_adjustment", "depreciation", "other_cost"),
                 "owner": ("owner_investment", "owner_withdrawal"),
}[key]
        title = {"discounts": "Sales discounts", "returns": "Sales returns", "other_costs": "Other costs",
                 "owner": "Owner investments / withdrawals"}[key]
        rows = [(e.get("date"), FIN_TYPE_LABELS[e["type"]] + (" - " + str(e.get("note")) if e.get("note") else ""),
                 safe_float(e.get("amount"))) for e in _ledger(db, *types) if _in_range(e.get("date"), start, end)]
        if key == "owner":
            for tx in db.capital.get("transactions", []):
                if _in_range(tx.get("date"), start, end):
                    rows.append((tx.get("date"), "Owner " + ("withdrawal" if tx.get("type") == "withdrawal" else "investment"),
                                 safe_float(tx.get("amount"))))
    elif key in CASH_ACCOUNTS:
        title = ACCOUNT_LABELS[key] + " movements (all time up to now)"
        rows = [(r["date"], r["desc"], r["amount"]) for r in fin_cash_movements(db, end) if r["account"] == key]
    elif key in ("customers", "suppliers"):
        title = "Customer debts" if key == "customers" else "Supplier debts"
        rows = [(d, f"{p}: {desc}", a) for d, p, a, desc in fin_party_rows(db, "customer" if key == "customers" else "supplier", end)]
    elif key == "inventory":
        title = "Inventory at cost (remaining qty x unit cost)"
        rows = [(None, f"{p.get('name','')} {safe_float(p.get('qty')):g} x {safe_float(p.get('buy')):.2f}",
                 max(0.0, safe_float(p.get("qty"))) * max(0.0, safe_float(p.get("buy")))) for p in db.products]
    rows.sort(key=lambda r: parse_record_datetime(r[0]) or datetime.min)
    return title, rows


def fin_writeoff_deleted(db, products):
    """Deleting a product must not silently erase stock value: log a traceable write-off first."""
    fin_ensure(db)
    for p in products:
        q = safe_float(p.get("qty"))
        if q > 0:
            fin_post(db, {"type": "stock_writeoff", "product_pid": p.get("pid", ""), "product": p.get("name", ""),
                          "qty": q, "note": "Product deleted: " + str(p.get("name", ""))})


def fin_journal(db):
    """One list of every financial transaction (sales, purchases, expenses, ledger) with IDs, newest first."""
    rows = []
    for s in db.sales:
        paid, credit = _sale_paid(s)
        rows.append({"id": str(s.get("_sync_id") or "S-" + str(s.get("receipt_no", "")) + "-" + str(s.get("product", ""))),
                     "date": s.get("date"), "category": "Sale", "amount": sale_snapshot(s)["total"],
                     "status": "paid" if credit < 0.005 else ("unpaid" if paid < 0.005 else "part-paid"),
                     "method": _acct(s), "ref": f"{s.get('product','')} x{safe_float(s.get('qty')):g} #{s.get('receipt_no','')}",
                     "note": (str(s.get("customer_name") or "") + (" | service stock cost allocated: " + money(s.get("service_stock_cost_allocated")) if safe_float(s.get("service_stock_cost_allocated")) > 0 else "")), "ledger": False})
    for transfer in getattr(db, "settings", {}).get("service_stock_transfers", []):
        remaining = max(0.0, safe_float(transfer.get("remaining_cost")))
        original = max(0.0, safe_float(transfer.get("original_cost")))
        rows.append({"id": "ST-" + str(transfer.get("date", "")) + str(transfer.get("product_pid", "")),
                     "date": transfer.get("date"), "category": "Stock transferred to services",
                     "amount": original, "status": ("allocated" if remaining < 0.005 else "partly allocated" if remaining < original - 0.005 else "reserved"),
                     "method": "non-cash stock movement", "ref": str(transfer.get("product", "")) + " x" + str(transfer.get("qty", "")),
                     "note": "Remaining service stock cost: " + money(remaining), "ledger": False})
    for p in db.purchases:
        paid, credit = _purchase_paid(p)
        rows.append({"id": str(p.get("pid") or p.get("_sync_id") or "B-" + str(p.get("date", ""))),
                     "date": p.get("date"), "category": "Stock purchase", "amount": safe_float(p.get("total_cost")),
                     "status": "paid" if credit < 0.005 else ("unpaid" if paid < 0.005 else "part-paid"),
                     "method": _acct(p), "ref": f"{p.get('product','')} x{safe_float(p.get('qty')):g}",
                     "note": str(p.get("supplier") or ""), "ledger": False})
    for x in db.expenses:
        rows.append({"id": str(x.get("_sync_id") or "E-" + str(x.get("date", ""))), "date": x.get("date"),
                     "category": "Expense", "amount": safe_float(x.get("amount")), "status": "paid", "method": _acct(x),
                     "ref": str(x.get("description", "")), "note": "", "ledger": False})
    for tx in db.capital.get("transactions", []):
        rows.append({"id": "C-" + str(tx.get("date", "")), "date": tx.get("date"),
                     "category": "Owner " + ("withdrawal" if tx.get("type") == "withdrawal" else "investment"),
                     "amount": safe_float(tx.get("amount")), "status": "paid", "method": _acct(tx),
                     "ref": str(tx.get("note", "")), "note": "", "ledger": False})
    for e in getattr(db, "ledger", []):
        if isinstance(e, dict) and e.get("type") not in ("loan_received", "loan_repayment", "fund_transfer", "opening_balance"):
            tag = " [REVERSED]" if e.get("reversed_by") else (" [REVERSAL]" if e.get("reversal_of") else "")
            rows.append({"id": e.get("txn_id", ""), "date": e.get("date"), "category": FIN_TYPE_LABELS.get(e.get("type"), e.get("type", "")) + tag,
                         "amount": safe_float(e.get("amount")), "status": e.get("status", "posted"), "method": e.get("method", ""),
                         "ref": str(e.get("party") or e.get("product") or e.get("account") or e.get("ref") or ""),
                         "note": str(e.get("note") or ""), "ledger": True, "entry": e})
    rows.sort(key=lambda r: parse_record_datetime(r["date"]) or datetime.min, reverse=True)
    return rows
# ====================== FINANCE ENGINE (END) ======================


def all_time_totals(db, up_to_end_date=None):
    """(gross sales, gross profit, expenses incl. other costs, net profit) from the first record to that date.
    Now computed by the finance engine so every screen agrees."""
    end = (up_to_end_date or today_date()) + timedelta(days=1)
    l = fin_compute(db, None, end)["lifetime"]
    return l["gross_sales"], l["gross_profit"], l["operating_expenses"] + l["other_costs"], l["net_profit"]


def capital_transactions_as_of(db, up_to_end_date):
    """(total injections, total withdrawals) up to and including that date (legacy + ledger)."""
    return fin_owner_totals(db, None, up_to_end_date + timedelta(days=1))


def capital_as_of(db, up_to_end_date):
    """Owner's capital at the end of the date: opening + investments - withdrawals + net profit."""
    capital = getattr(db, "capital", {})
    opening_date = None
    if capital.get("opening_date"):
        try:
            opening_date = datetime.strptime(str(capital["opening_date"])[:10], "%Y-%m-%d").date()
        except Exception:
            opening_date = None
    if opening_date and up_to_end_date < opening_date:
        return 0.0
    return fin_compute(db, None, up_to_end_date + timedelta(days=1))["position"]["ending_equity"]


import textwrap

# ---------- Colourful, Pydroid-friendly UI theme (uses Kivy's bundled Roboto) ----------
try:
    from kivy.core.window import Window
    Window.clearcolor = PAGE_BG
    Window.softinput_mode = "below_target"   # lift the focused field above the on-screen keyboard
except Exception:
    pass

class SmoothScroll(ScrollView):
    """ScrollView that lets a drag win over the buttons, cards and text boxes under the finger.
    (Kivy hands the touch to the child after scroll_timeout; the old 35 ms made scrolling fail.)"""
    def __init__(self, **kwargs):
        kwargs.setdefault("scroll_timeout", 200)
        super().__init__(**kwargs)


# ---------------------------------------------------------------------------------------------------------
# TEXT FIT: every AppLabel / AppButton / AppSpinner keeps its words inside its box (and on the phone screen).
# Order of preference: as written -> wrapped onto more lines -> smaller font (never below FIT_MIN_SP) ->
# shortened with "...". It never raises: a layout glitch must not take the app down.
# ---------------------------------------------------------------------------------------------------------
_FIT_CORE = {}


def _fit_core(font_name, px, bold, italic):
    key = (font_name, round(float(px), 1), bool(bold), bool(italic))
    cl = _FIT_CORE.get(key)
    if cl is None:
        from kivy.core.text import Label as CoreLabel
        cl = CoreLabel(font_name=font_name, font_size=px, bold=bool(bold), italic=bool(italic))
        if len(_FIT_CORE) > 150:
            _FIT_CORE.clear()
        _FIT_CORE[key] = cl
    return cl


def _fit_measure(cl, text, wrap_w):
    """(widest line, number of lines, line height) of text when wrapped at wrap_w (None = no wrapping)."""
    ext = cl.get_extents
    line_h = max(1.0, float(ext("Ag")[1]))
    lines, widest = 0, 0.0
    for para in str(text).split("\n"):
        pw = float(ext(para)[0])
        if wrap_w is None or pw <= wrap_w:
            lines, widest = lines + 1, max(widest, pw)
            continue
        cur = ""
        for word in para.split(" "):
            trial = (cur + " " + word) if cur else word
            if not cur or ext(trial)[0] <= wrap_w:
                cur = trial
            else:
                lines, widest = lines + 1, max(widest, float(ext(cur)[0]))
                cur = word
        lines, widest = lines + 1, max(widest, float(ext(cur)[0]))
    return widest, lines, line_h


class _FitText(object):
    FIT_MIN_SP = 9.0

    def _fit_setup(self):
        self._fit_base = float(self.font_size)
        self._fit_busy = False
        self._fit_ts = None            # the text_size WE set (None = we have not set one)
        self._fit_skip = bool(getattr(self, "shorten", False))   # the screen already chose ellipsis for this one
        self._fit_trigger = Clock.create_trigger(self._fit_run, 0)
        self.bind(size=self._fit_sched, text=self._fit_sched, font_size=self._fit_font_changed)
        self._fit_sched()

    def _fit_sched(self, *_):
        try:
            self._fit_trigger()
        except Exception:
            pass

    def _fit_font_changed(self, *_):
        if not self._fit_busy:        # the screen changed the font size itself: that becomes the new base
            self._fit_base = float(self.font_size)
            self._fit_sched()

    def _fit_run(self, *_):
        if self._fit_busy:
            return
        self._fit_busy = True
        try:
            self._fit_apply()
        except Exception:
            pass
        finally:
            self._fit_busy = False

    def _fit_reset(self):
        base = self._fit_base
        if abs(float(self.font_size) - base) > 0.01:
            self.font_size = base
        if self._fit_ts is not None:
            self._fit_ts = None
            self.text_size = (None, None)
            self.shorten = False
            self.max_lines = 0

    def _fit_apply(self):
        text = str(self.text or "")
        w, h = float(self.width), float(self.height)
        if self._fit_skip or getattr(self, "markup", False) or not text:
            return
        if w < dp(12) or h < dp(12):
            return
        ts = tuple(self.text_size)
        ours = self._fit_ts is not None and ts == self._fit_ts
        if not ours and self._fit_ts is not None:
            self._fit_ts = None                      # the screen took over text_size: leave it alone
        if not ours and ts[0] is not None and ts[1] is None:
            self._fit_reset()                        # wraps to width and grows in height by itself
            return
        boxed = not ours and ts[0] is not None and ts[1] is not None
        pad = dp(8) if isinstance(self, Button) else dp(2)
        box_w, box_h = (ts[0], ts[1]) if boxed else (w - pad, h - (dp(4) if isinstance(self, Button) else 0))
        base = self._fit_base
        floor = min(base, sp(self.FIT_MIN_SP))
        sizes, sz = [], base
        while sz > floor + 0.01:
            sizes.append(sz)
            sz *= 0.92
        sizes.append(floor)
        for sz in sizes:
            cl = _fit_core(self.font_name, sz, self.bold, self.italic)
            for wrap in ((True,) if boxed else (False, True)):
                widest, lines, lh = _fit_measure(cl, text, box_w if wrap else None)
                if widest > box_w + 0.5:
                    continue
                if (wrap or lines > 1) and lines * lh > box_h * (1.1 if wrap else 1.15):
                    continue
                self._fit_commit(sz, wrap and not boxed, box_w, box_h, False, 0)
                return
        # nothing fits even at the smallest size: shorten with an ellipsis instead of spilling out
        lh = _fit_measure(_fit_core(self.font_name, floor, self.bold, self.italic), "Ag", None)[2]
        self._fit_commit(floor, not boxed, box_w, box_h, True, max(1, int(box_h // lh)))

    def _fit_commit(self, size, own_box, box_w, box_h, shorten, max_lines):
        if abs(float(self.font_size) - size) > 0.01:
            self.font_size = size
        if own_box or shorten:
            if self._fit_ts is None and not (shorten and tuple(self.text_size)[0] is not None):
                self.halign, self.valign = "center", "middle"
            if self._fit_ts is not None or tuple(self.text_size) == (None, None):
                self._fit_ts = (box_w, box_h)
                self.text_size = self._fit_ts
        elif self._fit_ts is not None:
            self._fit_ts = None
            self.text_size = (None, None)
        self.shorten = bool(shorten)
        if shorten:
            self.shorten_from = "right"
        self.max_lines = max_lines


class AppLabel(_FitText, Label):
    def __init__(self, **kwargs):
        kwargs.setdefault("color", TEXT_DARK)
        kwargs.setdefault("font_name", "Roboto")
        super().__init__(**kwargs)
        self._fit_setup()


# Optional Material icon font hook. Plain Kivy ships no icon font, so by default
# badges show short monograms. To use real Material icons, bundle a Material
# Icons .ttf with the APK, set ICON_FONT to its path and fill ICON_GLYPHS with
# {"icon_key": "<glyph character>"}; badges then use the glyphs automatically.
ICON_FONT = None
ICON_GLYPHS = {}


# Embedded PNG artwork (base64) so icons always ship inside the app: no separate files to package.
ICON_DATA = {
    "debts": "iVBORw0KGgoAAAANSUhEUgAAAKAAAACgCAYAAACLz2ctAAAZXElEQVR42u2deXRcxZ3vv7+qurfv7ZZkC4ONl+ANs8gQ22DAQMAbgXcMhJdkpMybl8CEmZjk8MI8QoA5ZHKaHpZMQgI5Jy8E/AITksAM3WEmMMQJQ8A2WWBigxewIQTj3cY2WLak3u69Vb/540pCdgyWZHW3JNf3nIaD8JHkW5/+/pb6VTWhQkqn0wKYJzKZ+VHPr99724axbMwMYsxk1mcAmMKMsWBuBCEFkAIYVpUQAeAIjDyIWomwC8DbRPI1JqwhIdZ+5e6mXQev4zIFLDeZTMZU6jcaYPBYTN8AasmR7voZ3/37N2Yz68sYvICN+aiQcpSSLgCGMQaGNdhoGGZY+CoPoSACCQlBEkIIAIRIBzBav0dCrCPQ80Tymf/7T6et6lqQbDPL9U3gTIbMoAQwnU6L6RumU0uuRQPAfbeunsRw/4qYW0iIGQk3iUiHCKMytA4ZFP9FiJkYICKqyBvC6rBiZgYBzETc+RUhpUOOSkBJB+WgADZmLRNlCcFjN35z1uYYxKxc37SeB8oRB2LBKZtl0dISO959t702k4z4smHd4rl1dWFURhAWmUCaCQSwIJAFbTBSCWaADDGYwdJ1fHJUAqWgo0OQzLIw37vx7jPWAEA2y7KlhczRhiw6Otdj0WXJ3/rqqqmOk/waDH/OdX1VKneAjYkAFiASdnmHpE8agAwJobxEHYKgGEHQT8KwcNct35698VAGqgpgOr1MZTLzo8WLH3ROP+7CrwL0967jNxRLbWBmTQQB63TDKWIbIpK+14AgLLYB/E+v7/vdt5csuS7sYqFKADJlsxAtLaS/efOqs1yRfCCRSJ5TLLWBjY5ApOyCDWsWIxJS+V4DyuXCysAUvnjrPbNfiUMyDEBcMQCZOa4UiPjem9d8UUj3PimVVyrnIxCkze2OoVyRob1ESmkdlYwObvzKPTMf6MlHb79Xr3OzdJoFEXFLS07ce+urD3jeiB9oE3qlcl4TkbLwHUuNHCIiUqVyXmsTep434gf33vrqAy0tOUFEnE6z6P336kOxcc9Nz6SEGP9E0q+/rKPQGgEsiYjYtu6OTRCpMzsE6bpkoyoU258xZsenb/7OZfneFifUW/jSX36pYYRf9x8Jt+7ifHF/SATHLoHV++kZwpQ/0ikHHS8cKHZcmfnenLbeQEi9yfluv355qr7u+KW+W3dRDB9Z+KwOx0uY8kc6xaDjN+0d7y66/fvz8kfKCdWHVbu5HARyQP2k457wE3UX5QsWPqsPC8nk5Iv7w1Ry5EVg80SuBYvQDAD8gdWx+ODQu1y2tJDefNLa+5PeyEstfFa9hrCwP0x6Iy/dfNLa+1taSKfTy2WfQnBXY/GbN728uM4/7sFC6UAIsIXPqi8ohklvhNNR3Hfdrd85e8kHNavpg4qOb3315Y8q6f2BjVbaRKJrWsDKqpf5IEuhDAkZRbp07i3fPnvd4YoScWjet2FDjh5cvMohpkeUUAltIlj4rPoRikmbCEqoBDE98uDiVc6GDTkCmD4QwGwWIpdr0QfqxE2pZOPMUpCPiEjax2nVTwhlKchHqWTjzAN14qZcrkVnswczJ3uG3uuvB/ulK09Swn08isqK2djQa3XUHGodsZDyggUf+5ufLv67cQeA28WKFRk+yAGnb8gRETGFdIfrJFNaawPEuxz2ZV/9fQFEWmvjOskUhXQHEfH0DTk6qAjpTA753ltWNzE7a40JieP/Z93PakBqEgJYCIeJwhlf+dasDek0UyZDRgDA9Ok5AsBhZG52XV8yw1j4rAYyDDPDuK4vw8jcDIA7mQOl02mRyWTMd25cPd5I8SYAn9nAAmg14C4YD8YXhTan3HTfrB3pdFoI4HYBAKGgq/1EfdJooy18VpVwQaON9hP1yVDQ1fGXbhfEYMo158SmCVPXuk5yehCVdM/q2MpqAKVd5ckgLKyfvH3jjOZcsxEE4o1jp85UypteDots4bOqoGQ5LLJS3vSNY6fOJFA8uUqKFrluEoTuw+RWVpWJwyDtukmQokVAdx+QFmodIj63a2VVyUoEpHUIgBYCAN11w4tjlEy8LqTTaEzI9iilVYURZCEcMjpsjXT5dCWVP1NK1ah1YOGzqkYQJmNClsptZBIzBWBmKemCQcY+HKuqeCDIxJdTmVmCDJ1pb6Syqg2GdKZg4qnGGBDbAsSqSkGYQcYYMPFUBWCsju/mI1sEW1WnDGGKN9wwVhnQCDIaduzPqnplCMEYDQMaIQhcZ4cPrKoehdmAwHWCIOzWm1VtKISQwlbAVrWshBXszUJWNZS9OtfKAmhlAbQa6gk9Dc2dfGUzwOEBXxDEW/luQsKYobOq1gGHA3xlg/MWjMFHptah/UAIGkKfxGIBHPIAEqKQcdLUOnz2hlMwZ+EYlIsRooghBFkAraoAoQBKRQ0pCZf/r5PwmetORqreQSEfQQxyN7Sf6TFcqslOt4sig1NnjMS4SSn8KrsV61e1IuFLSEmDMjdUdiNkiIsBmINBNIZRP8JB8xemYsppe/Hcv+9AqaDhJSWMHlwLbkPwMHXD+HIgxtkXnYDP33wqTjq5Dvm2cNC1ayyAw7g6jseeGCeM9XHNjadgwVXjEYaMMDAQkiyAVtVzQxKEuVeMw+dumIbjxnjIt4eDokCxAB4jbggAxjAmnlKPv7nlNJwzdzSKhQi6xu2amu6E9AwTbA+F9rsG6e0aCkFgw0h4Elf874mYfFoDfpXbhvbWAH5KwTBXfTqvZm0YIQhhYBAGcXXmuAJRaGIQYacUew1g902kvXzTCwIYMMyYfnYjPjIlhaX/uhUbVu+HV4N2jaoVfKVChONP9HHu/NGYdEodEr5CUNaWvP5AaBgNjW73sz0yhYDojDwNjS7+8ksn47+W7cHzT+5AqVjddo2qCXzFCCefMQKfvnYKvGTPEwH2s3BqUaAAwHnzR2PitDr84rGt2PKndiTrFAACV3hgWS48b/Ht1cv5CFFocNwJHq7+u1OQ8CW0ZnsibwALjf7l4ehsXruYMWcUYIDNb7bDGIZy4rxxWDggERCWNS74+Bi4XmzzUlr4BpMbSklY+MnxmHxaPZb+yxbs2VmEn6ocJlVtwxjD8HyFidPqgc7elNXgbNdMOb0B195yOs6+6ISKdieqCiAz4CQEEp60p5AHuRvqiJGsU7jqmskYNymFMDQVSZWqG4IFUC5qFDoipBpswTEoK2oGAIZUhD07iviPRzdj15YCXFdUpCBR1TyVKYhQLkV489X9GD3eh7Y54KCSMV27IoSVy/fg1z/fjnLRIOEJmApd3ldVBzTMcD2JF3+9G2ecMwojR7mdVbCNyAORwPU7QnY2poUgtO8PsfRft3TPEXp+Zc+YVLcPyIBUAoWOCI/9vz/hL74wBaPH+RaeWoZcwyBBEER4fXUrfvn4Vux/L0CyToGZK74rQnd9+eWq7z2QIIRlDdeTmHHeKEw+vQHJlB3O7m/lqjXjhLEeUvV9y6u7Qm5QNnj2iW1YuXwPpCPgOKJq23E1ATB+cPFWULmoQQLxfBrDxuJ+VKyF9gif+dJUzDz/+B553JEKjRjerW914OnHtmDXljyS9Q7AXNXbWmpmO8xx7pes6zwVYO+o6TeAUUL0eqSqC1BmYMUvduKFpbvAhpFqcGoyrl/zuDeUDlEP1rZJb967zPE/hCC8+04Jv3hsC95afwB+SoEcUbOzIjbxOpbaK0R4+bd78ewT21HKR92uxzU0AQvgMQJfvj3ELx/finUv7YvbK0k1KE7IWQCHe3tFEP64bj+W/stWtO4tI1mnYAzH8A2Cgk/Z3L//7Y/uzm+VK8cj5YBdrhcGBs/9+3a8+NweSEnwUwq6p+sNgrW3Dtgf8ABEEUNHBgBDSgHlxDlWLfOpLhilJGzflMfTP92C7Zs6OodLMUhvRrDqU8ujXNJgBo4bnUDj8QkQAfvfC/De7hKYUfGtqw/L9YgAKQi/feYdLHtqB3RUu/aKBbAC8BXzESZMSWHu5eMw+dR6uF58nCAMDLa+1YEVS3di0xvt8FOqqk7IzPCTCm37A/zbw5vw1mtxe0V6YlDDBwB05/952WaBvYTvzPNG4ZOfnwSlRHfIw8GpIJ5+dAtWLt8TH3OsAoREQBQyms5uxI5Neex9p4RUvRr04HU/W4vXkRe4XNIYPzmFT187GUq9v0/a856Vrq9d+dmJmNrUgFJRV2XimxlQDuG1lfvQ1hogVTd04LMA9pJANoyFV42H6Dwze7htr3h7K174Sz45AUKgatuLzICbEJCKhtzOkgXwSOEtMBg1xsekU+u7QfuwUA0A4yalcOKEJMLAVO22h74eULcADhECo8ig8QQXyhG9WuCuanTUGA9RZI+cHrEKZtuJ/hBbwVGcg2Awv/+ysg7Yr7imlMD+d8vQEfcqnHaF4X17y5CSLHzDEUCi6iX3yhHY+04JWzd2HFTtflD4BQPvbCtg17YCHFfYMcfhBCARgwGUA7eKPzT+1/NPbu/8HQ5faXZ/jYDnntyBKDRD4mMSLIC9/UWFQTlwoYTB6ZM3gbk6i8uG4fkSm//Yjqd+shlE74dZNu/P0onOyZNnn9iGN1a3wk8qO2zbmyJksF+H1hVu8wUfJ456D3+xaCnCko/1G6fAT5SrAqLRDC+psHLZHuzbU8b8T4zDR6bWvQ8iAzs357HiFzvx+iutg/I2+sEL4CB3vTBSiCKF82euxccv/B0SI9rwx1enVy0P7OmEfkrh7dcPYMub7Rg93seoMR6IgH17yti9vYAwNFXbgrMAVjjtImFQKHoYWd+BRfNWoOm0N8DlBLjkQojaLLAxjISvAGbs3l7Azs35+I0iCY4r4DsWviEPoCCGNgKloo8zp/0Jl89fjvoRB2CKPhiAFLVd4K6cz3EF3ERXCI4HUi18/QBwsDwy6gy5xXICnhvgqgXP49xZawAjYIo+hDAwnfkeH/KqCYgMe5R0uDhgVz7XUUhiyoTtuHLh8xhz4jvgot+dC1pZACtWaAShAzBh4ZyXMP/8l2K3KyQteBbAyroeAcgX4/bKlQuWYfLkTUDJA2tp4bMAVtb1okghDBXOPeM1/I+5L8Dzi92u15sWiyCG6NwZseqPA8QX8RhDNQawmitIgCCDYtFDfSqPT338WZw5fQMQuOCS12vXM0agWEyADVVtR2S4qeu5eYlyvMVZo+dYNQcUxNBMyBeTaJq6EVcuXIYRja0wRT8Ox72Aj4iBSGHCmN34/CefhLRhuu/gdRpBqexi047xWP/mNIShA8cJawIh/eOXVlXcA4UwKJVduCrCwgtewgVnvwIwwYRO/3I9YQAnBKz7HV0IJmDXzrH42S8vw97WRrg1gLCiDvj+Pm4SE8ftxCcueR5jx+086vYKGwEuevYuwaOywvjhjR27C1df9RQezDajWPIghalqVqYqCV8YKbAhzDt3JRZe8CKkEw1IeyXeqrPlx9EXIYAuJDHihHdx8exX8NTzc5FKFsGmekNSFbkbhogRhAoj6jrwiYXLMG3aW3F7JXBse2WQSQgDDlycMmkzfO88aF3dCT1VCfjCSOHE49/DFz6Tg+MXoTtSkEpXfYLFqndOSExIeSUkE2W0F5KQUlctFxxw3JkJSmrs29+AXy6/GMX2eshkEcbY4yeDORcMI4UgUlVvyVSMCsMCv18zA0seb8amLRMhkoVuQK0GEX9MgBNhx+7R6KjB9mdFq+C6ZAHv7R+Bf/7Z/8TF567CgvP/K97nDdyj/otakI+yAOG4iU9SA5HECy/Pqkl+rio50GQMwVEhAODXv5+DTdsm4KpLlmF0j0mXfuWFxPGDszqqsEtOBI4knvzPhdi8Yxz8RLlz5K16uTplvriyKj8tbkYnkHADXPqxF3HerDWAkTCh6ts7jxhRpFAo+t2tBKveghdfN+I4IYJIYfvuE/D7l8/C253w1SKqVG0rzhgBzw2gjcDPn52Pt7dOwBULVnRPOwviIwJlmCDcAJs2n4SfPr0InhvYUNyP6OGqCKFW6MjHOV+y2/kwfAHsBogYqWQRr755Mra9cyKumL8CTaf9MR5I0KJXDWZmQhiquGtvAeyzgsAFEcNLlLvXpVaq+iXlDABawPdKyBc8PPrk5Ziz5SO47OLfwfXKMKVEr0IyEdu+Yn9NkAwGwyhW1R3w0JAspYaUGr97ZQY2bR+Hqz6+DBMnbgWXPIDpQwHruo7MHsvoF4KD5jepaXeYO1sBqWQRe/Ydh4eyn8Ly31wAkhrkhLZ5fQxoUKywMQKuE0JKjV/95kI8lP0U3t13HESy2A2plQWw4m4IAKlkARu3jccDjzXj5dUzQIkySGrrhhbA6rmh7wWItMTPfnUJHn/qcnQUPQi/ZCEchhqUV3MYQ3F/yi9izeunYtvOE3HlwuU4ddpGgLimbQOrYe6APUOyMQJJv4i2fBI//vmVePrZBTAs4LmhzQutA1YvJCuloaDxwqqzsPvdUZg2cRuU0mA7k28BrGaBUp/MY9OOcdi8YyyUiuyhpOEA4FBq5GoW3dM1NgRbB6ypG1rZIsTKygJoNdRDsN3Nt7IOaHXMAshge7jCqjYFJVgLMDqIRPzfVlZVYo9IAIwOAeCAIAF71aNVFZ0PIja9A8oAu0DqJOaIQXZvy6oKADIxSJFBuEsQeKMQAkTWAq2qIyKwEAIE3igg6FVrfFZVhzC+r/lVAYPVkQkAsG3JWFUrCIvIBIDBahGxWaOjoFUIh+wZM6tqZIBCOKSjoDVis0Z846Hzd4OxzpEJgMn82edg2Zd9DeiLTMwa1n3jofN3d4Xd56RwwLYXY1Vx/wNL4QDAc0DnVhwTLw3CAgCW9hFZVRhBGYQFMPFSIN6KozcObF0TRqX1ruMTALs1Z1UpadfxKYxK6984sHUNg0kiPU/df/8Vet5Zi0ck3NTCICobIghbjlgNaNuFAMMwnpsSURR89wc/vfQFpOcpASw3AOAq58fFUntBkJA2F7SqRO4nSMhiqb3gKufH8VeXx9cjZZuzsiXXov/h2pd+5HsjrymW2iKioTeubzWoAYx8r0EVS/sfufPhOX/dxZwAgPVNzfFHJ4rEPUFY0BSPx1gXtBow/ohIBGFBQyTuAUCdzMVVcCZDprk5K+784az1kQ4f9RL1gtkWI1YD5n7aS9SLSIeP3vnDWeubm7MikyHTDSAANDU1M4NJKfn1IMznhZDC7oxYDQR+QkgRhPm8UvLrDKamTvc7CMBMhkwuC5FZMntrFAV3+ol6YawLWh2lDEP7iXoRRcGdmSWzt+ay6HY/4M+uymRqbs6JSxqniO2R+YPrJmeWw7wmkG1QW/Xd+8A64aRkEBTWTFDi3F+3vm1yuWbT8zb6QyZgiJuamvm6JbPDiPQ1WkdlSQpsQ7FV3+FjSQpaR+WI9DXXLZkdxqH34HuX/2wEK5Mhk567TH3jofPX6ah0Q8Ktk8QU2Udq1RcRU5Rw66SOSjd846Hz16XnLlM9Q2+XDhtaV2x5xKTTy9Q/fveilXPO/Oy4pDfy3CAshh/0562sDi47OEz6I518qXXJnf88J5NOL1OZR+Yf1sQ+ZBSaKducE0AzXm1YudRLNFxaKLaGRPEog5XV4eEzYdJvdErltv88s+2cRUAOLYfkfb0EEGBmAgHXNy9PHd9QtzTh1l9UKO0PichCaHV45/NGOuWg/TfvtnUs+n5uXj7+eLAP/ryNDx3DJyK+PQ26Pze/g0r6inJYeCHpjXSYObSP2+qw8IWFF6ikr7g/N7/j9jSIjvBpQkc8B5LJkEmnWWQendOWL+1dVA7yz6T8RocZEbOtji14zMyIUn6jUw7yz+RLexdlHp3Tlk6zOFzR0acQ3FNd37C5OStPq5/yfS+Ruq4UtMOwsX3CY7fVogUJ6bn1KJXzD77R/vb1uVyL7i18fQKwZ05IIP76tSu/KKW6TwjllYN8RAQZT31ZHRu+B51wU8qYqKR1dOMdD5/zAIPpSDlfn0PwoTkhAcg2s7zj4XMeCMLihVpHK5PeSEUkiRm2Xzjs0UNEJCnpjVRaRyuDsHjhHQ+f80C2mSWhb/D1GcBODLklRzo9d5m6+0cXvLJL/OHCctBxmyTZ5nsNqsua7SDDMHO8zlvUfK9BSZJt5aDjtl3iDxfe/aMLXknPXaZacqT78wniRxUye8b6r13926nKTX6NGZ9zHE+VgzwMmwjMonO+0GroYWdAZAQJlXBTCMNSRISfREHhrrt+/LGNhzLQHw1EzkbZZhbxOwBI/+3qmcz4smHd4rmpukgHCMIiA6SJQAwWZHPFwVpUMIFMfCSDpev4pKSLUpDvECSzRPhe5oez1qAzDWvJkcFRDi4PGAjpdFps2DCdcrmWGMRrVk8yUv8VCC2C5AxH+TAmQqjL0CZkQvyu6SxsqPN+Ggtm1VI5BhjclbMxWEjhkCMTEEIhjIowrNeCkRVaPpZ5ZNZmAGhuzsqmpvWcyWTMQPwiA77g6TSL6Rty1NIJIgD6+hdemQ3NlzHxAjB/VJAcJaXb+Z7TMEbDsEHcVrSpY2VFICIIEhBCgkgCIGgdwLB+D0TriOl5SHrmjv9/1qquBck2Z+X6pmY+mnBbFQB7OiIwT2QyB29C37Z41VhH0wxjeCaDz2BgCsBjwaaRiVIEexiqsmEWETHnQaIVoF0EvE2g14SgNaHktXcvmb3r4HVcpoDlZqAc71D9Nwgmw+X0jUJ6AAAAAElFTkSuQmCC",
    "support": "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",
    "cashier": "iVBORw0KGgoAAAANSUhEUgAAAKAAAACgCAYAAACLz2ctAAAmQklEQVR42u2debRlVX3nP799zr3vDm8sLKpwAgc0VDE4UEyiJUGEZBGbtCmcJ2zBhWatTpvOsNIKJHGZ1Ykr3VmJEUxjEm2NVbZt0hhBIGWBIlhgwhBKBEGgoKooqDfe8Zy9f/3HPveNd3rv3Tff31pH4HnOuWfv/d2/ef9+whKQ7toVAMiePXbyb6dflD8WFE4HOV2Qk8tWzzNCSuE1gUi/VVVA6NJykAYiYlXHBH7mlCgTyF2KPgr6wCabf0AeuLXQbD07RdJx4O3Z4wQU4PnTdr7UBO5CFX2zUy6wqq/ImkACgUgVgKpTLNpF3nIjEAgQ0sbPfEoEq1ByVgORJ4ywV1TudNbc/qIH9x1MnhF27TKdBGJH1n03u4JdTAHvyBlvfnsovN+il/WaoA+g5BwVdSj+fxCR5AOky/lWDoearBmqiiCCmB4xZI0BYMLZ8QD5dqx8dcv9d36vBsQ97DKXs3ggyiJ30YwdceR1b/qgUXl/aMxFaRHGrcWqswKKiAFMW1PSpaUlabnsDlWnIIGYoC8IqKoSO3erE/3qln/74d/Xk3jLCkDdtSuoAe/waedeGJrw97OBuTBSx7i1KuAQMdLoN1T9VZsMY0AECYIuQJYMeIB1qHNT8z99DeoAU0ETMJq+IJCUGErW3R67+HNbH/zR7bOxsCwA1J07Q9m3Lz7w2vNefFyP/LER+UhKhHEbx4CISNCUuxkDQYCkUkgqBYGZAp4xXaAsudBVcA61Fo1iiCI0jsG5phxSVS2gfUEYRqo41S+/UNH/dsojdz1bw8SSAlBB4BoRrnNPnX7uxT2YL/cGwQnHbOxQ1YbAcw6M8YDLZJB0CoLA/7p2Re+KiuHaGjiHRhFaqaCVCljn76nHFVUtIrIpCM2EtYcquI+8/IEf3aJcY+A6nY9IlnmAzwg4gGdOO/faniC4xqlSdi42ImFD4IUB0pPBZDMQhsmAdRFaQ5eWHJTWopUKrlSGKAIxdZHiVOOMMaERoWLtdS958EfXzsZKRwCo11xj5Lrr3JOnnT+UEb7YGwaXH4sjlzjuTF02L4LJ5ZBc1nO7Guvv0toAoojniuUKrlAAaxvpiE6ATWHKTMR2d1n5+IkP/mC4hplFA7D2ogdOO3/oeHG39AfhjqNRFImQEpEpUNX+XRXp6UH6epEwnAs86XpcVr2OOAuI6hxaKKDF0sy1Tv5dVVEl2pxKpcZsvP85NRef3iYIpR2x+8Bp5w9txt2SC8yO4TiOjEiqIdfr60Wy2a5et97IGLRaxY2OQRzXNRadajQUhqmidfuPkoCwhTiW5gYHPHXa+YMh7pZ8EOwYiaP6+p5zkEphBvq9Vetcd8HWq2h2Djc+jpbKjUAYD4apsGDt/hhz8csf/MFIArS63Kixz2PnzsCAgv3SQBjuGI6jSERCTYymycspZDOYTUMQhp5dz76ne62PSxUVQQYGkN5e/9+z7hGRcDiOooEw3AH2SwaUnTsbOndNMz/f46ede+2mIPXOo1FUX+w6h+SymMHBrsjdYHqi9PVi+vvqrrkRSR2NomhTkHrn46ede63s2xfrzp1hWyK45tX++alnX9Rrwu+VnY0VwjlPOfXg6+8H7YrcDasXFkteL6xjXArEGROEEy5++6seuufWehETM9voYM82fWLbjq1pMV+J1amrxyWtQ7KZZAd0wbdhqSYB+/vq6v0OTKxO02K+8sS2HVvZs011Fp5mgmvXLhGuc86YP+kzwZaycxYws/UA0mmkv6+uDtC9NtjlHORzkM/NwQNgys7ZPhNsccb8iXCdY9cuqSuCa+zx8dPOfUsO2VtSq1AntCaCOW7Ix267Ol+XpuHCvjCcRE5mi2O1WQmkiF7wygd/dMd0UTyl2+3Zpnt37gz1+fIfmSA0zmHnvkcxA/0QBt767VKXpovTgX7sseE5jEkVjBGj1v7R3p07L2TPNjeDA9as3se2nfWeTWHqa8fiyBqRQGc6eDC5DGZwAHWum0HapYZGiR0ZneEj9Dar2k1hKjgWR+999cM//noNc54D7nurg30AV1b92Yy5XsPAeN9PomzqKhr0RjcEVtW3ZDNIqYxWq5OiuIaVBFtXAl+vYU5q8vjR7WddkDfBvxSddT79YUpBVKcEA31IPgurSfSq+tShjagNJGlU0pNeXZtQBKKI+NgwgsxiVupyJjAFZ3/55H//8V7dtSsIv//cc5Ks5ZUpMahaJ+Kt48kHU6GP764W8Img1hLk87zos59JYs8b7FCdej4x/MW/ofLQgWR93KpgCqTTSCaLlkozDBJVXEqMUbVXAnu//9xzEl6wb1/8xLYdWx3ya+M2ViBQnTwzhDpH0NeLJs7n1ZLNos5BEJA950wwGzeN3/T34+KYVaWIOIfJZYhLpSkp6jW7YNzGGiC/9sS2HVtfsW/f4RAgFrlo0AT54TiytaxmnZY+L+n01O5aRa4XVcVNFDC9vTPPNmwU3c8Yn0pfW5fV5BYLQySdQivV6esisXN2KEzlR5xeBHwl9GPRC9RMwUumsXnJ5iAMVm+GizH+2mgArI19lY5ZESSTwZUrU9J0GgtzTi8AvhI+tG1nr2rpwpKzqEggM5RGwWQyU9xwVQ2wm9U/fR5W3Vyo8wZSkiE1+WeRoOQsilz40LadvSaUwikp4cWVeqUxwhBJhd2IR5cWRkHgD6DNlJ5SUdWU8OJQCqeExskb00bCgnNOQHSaySKZHlTMqhS/7ao8cRyv8TUMJkVYIxY4ORerjU8okEqjlGYslgPNGhNaJ28MneopgqDe9J2xwiZMr1ox1858x3HM/v371yQIRQRrLWeccQaDg4NM90ysCRGcGEqSCtFZ362qKghO9ZQQYUfsFXiZreBKOlzz6fXVapUoippzkVUKwDiOcWv9eEMQeCM2tjMG5zHHjtDhz3jo3BlAV3GYq91dn06nMWswXCciBEHQ8ttXNQdMcEQQ+AoMs0JzLjk3+dqKTyqd4bKWVGrKvbFGKQxDduzYseZ1wBog1ySJIEGIanmGP9BjTl8bBir91mNyhgGSyOpVC0B/FlXbAuG6dsPotLlYjWtVS1Kd+X1igQDpD2NU51SwqnHA6QeQ1+wCre3vl7XuXJ+OpdlGIqrhDM63AB1rteuAsgGiI2t4rSRc74uz7v2Aa5xCXcO7ihbf2PUDrn4OHdbV8aZXz1ytOlTN9d/i89a/H3CNrFWDb1vTHLDrB1wPHHAdU9cPuIZ1wPUEwi6tHp19NnUrgq/n1V0THLCBEbKqveu0HwlZ/+Bb22vV5YBdWp064HqxgjeC9G3HJ7pa16rLAbvU1QGXRAec7ym56dX+V+MzjbsXzbi6OuAqUMprC6btZhPXFniJn1E3rftQm2CZfGad9llZkzqg833KEBTnHFJrvgeTPeeqzx2l5/jNuFYLp4oJAmw1whWLpAYHWoe/FvIMYIwhGhnF5HIE6RSuQfOXSRLBGEPluaOkj9/sf7r2TPJ7VpUYz2FWKzdZNzqg4htO9AYhg2GKnAlJ9fZijMEEASYIkGKZY5/7c56+7H0UvvlPmGQRG15BAM8c4vAnPsXB93wUe++/Nr9/oc8Yg733Xzn4no9y+BOfgmcO+W9u9owIhW/+E09f9j6Ofe7PkWJ56pkwxBhDPpViwPj5gDb7Y60ikvtOfr3W2+HSkyYcGlo1bN+pkhJDWoQfTIxwx9gxnrQRvadum2oFJkL18BHKjzyGyedwpTL5N5xBkM81FaOlRx4lOvq8b6YYBOTfcAbSKAa7kGcSUVr4yf1Jh8qI1OYXkX3tyU31O1soUvjJ/ZhsBlcoknntq0lv3TLF7UWY+NljHFcoc/bgJi7q30SPGIrOEqyW0J0xuPEJ7Ph43Spect+rX7fqAehQMiZgNI759MHHuGN8mEiVEMGWZp45lVTKN0a0DozgCsWWOprJZKYO4CvYYrHluOf9jAhBLpf0hxc0inHlcnPuYAwmn/NFoQKDK5XRKJrzHRoYVJVfyub5w5e8itfl+xiN49UBQmNwY+PYiYn6ALy3HgCTCUu96LgVrz2iQCBCwVp+88mfcm9hjOOC1GTrnTlcR9WXD57swSytx+DcFHaEppxsMc/4RtHTjOBWz0y3HhV8+2+Z805JmOiYjRkMU3zhxF9ie66XkrOYlS5ZJ0I8MoKWK3XXIWw6eOdWvIO5Q+kzAZ999nH2T4yyJdVDVacWEmsbI3e622M+iLd2dT7TrD6jQn8QMhJHfOaZn/O1V52GQVa+aqLqlOE0HysY59BqDPmV6/2mQEYCHikV+d7IC2wKUx58DSgw679AlgLO1rcqY1X6g5BHSkVuHT3GZZuOZ9RGBCsJQWvR2M7fDQPgogpGMyv2+U4daRPwk8I4Y9YyGIbYRg5NgdGC7xKwbgulqpfa/b1+vHVjCICI8uPCCP9haPPKFo4VwVUjz8waqEJhQxElgq1GmKT54ApxbwQ4ElXQFl8xXoJLz1POPhU0Xn+cUNUrTE8+C9+4TYgspMO5Utm3IhKOVKvEibRYsQiJCK5a9b/fwPneNFtT4xiNYl9iawWt4bAJmozARAm+8J8dH333BkhPMPChS4Rf/wNDsezLrtRbmlBk5QWBtbhqtamx1TwjWhVXLhH0pFcUgNpE5xstwK+dp3z0XYodTVrXrWM90Dk45zzlt9+l/M5fC5sG6tsyK74VRXDlii8h3AyArXw4tlzB9NoVkWmtwoEiEMXwptN8BMA5SK3zDHwr4IrwplOVMJTmUUZWLqQqgC2XWuImbKkfWIctl300Ydmt4famsBolfeE3SIloY/yYW0uNFYKfCC6OcJXqNAW2oUbRGsq1aMJq1bBkA/YNa2fMK7FeWjNgC8W21LbWp+KSsJEtlgiSlpyri/91aVXNX2L52lKprV3SXjaMEexEAbWuC4YutQR8PD7Rts3a/rlga4knJgiTbpmrwQjp0irjgMbgiiVcueKb6LQFwHahmsh1Sad9tskygHAy1byLpdU/fyJoFBGPjvmoR5u4MvP9kXh0zPt2pNsxuEszKR4Znbd0nH9pDueIhkdJHTfUFcFrRPwu9RyKMcQjo7hK4g+bj9ReEKutVolHx7vNorvkgxWFone7mPlLxflzQPUpGbZYBCAY7J/MCu50CKzrhlml86dTnM8WisQjowtuGBkuKMab/JAtFFCUcGCAdopFLtUMbsQSMW2NeSl3rzHYQoF4dGxmpss8F2Nx5dmSHaBOCQf6O95XpO0ilCmflrRRgOicH/OKcUARbO2cxyKN0bATO8GVSkQ2JhwYmNncehm4QCqEHz4I/wVQA3HMus+GSefghw8Jy+6MSM4jxyOjuFKpIzZAZwpUGoNGMdELxwj6+/1Jrg6c5G+1g62D/hx850fC//qGbJh8wLvvEv7sG0Jvi/yQjnFAEUQEV6kQj476tlsdMkDDjsktEVSVeGQEUyoR9Pf5BiWLAWIbfUidQi4DV/8Pw3fu2TgZ0bGrnxE9Z+4Wu77GoNZiJwpTR087qGp1rkTvtKI7tlLBPl8lyOcJclkIwwVNxnx2b18WbrpL+L/72BBnQlJh80Nyi+KACcdT53CFInZiYiqxtMPds5YmfTNhP3Z8HFsqYTIZgmxmZvuveQyinTudwkB+A52KazEpbqHrJqCxxZbLuFIJrUb+70vk813aIuXGd1u3ExPYYhGTxJFNOu3PG7cw30V8SY4T0xl/tLDFrFvHhicRX7DoxHSGVKIW1d2Vyd+kdo9zuEoVVyljyxWf57+EwFtaDlgPiICrVHw5iiBAwgCTSnkwGt/UWKbdCyAIZZQz8v0cn+5hPI4IRLqO6RaqUEoM5/UPYRFfTWG6TpJIH41j1DpcFKFRhIsjsM53ZDJm2aJc4bIf2UtMea1Yn7aTnBeVZLfNrsRQBl5kDJel8/xldIzjJfTlyLpQm0Mp4AXneEs6y+tLEceKR+fEWtU5X6lgupEy/cxujSMuE63cEZ5ZB5VVFeLYK7uzaBh4d5jjuZ6I3dUJBkRI0c3Gma3zHVXH61M9/NfsEOVyebKc3XT9UaaJX9qpm7PkHHC1KTANqAr8ZnaQzSbgH6sFjroY28Wd13CAXvFS4j/1DNAnhjK+YKUuwKBb1iW//eXb1oQ0q31knxgOuZgHbZWnbITZwHmJgq8Hs9kEnBr08KogRUkdMWun8uiKc0CH0u4ZfkUZdpZ+MfxymMWksl2rN3FBVVFGnMWIN94srd2hmsz9Sm7hcKUi+Jrs0pzIPD7B+6lQkrrIXfFbA6EB8rWiiW1rPEKkykqGz8OVOjsaAiPq+IvSKDHaNSlWALQlVT7Y08frwx4KK1TkfEWsYAfkxPAP1Qm+HxXJiaHrQ15+w6WI0lMVTg97No4OqHh/1SEX889RkUETENLNel4JyiP8JK7wcFxle5imuAJccNk5oFMlawy3RhWOuJgBMV13ykpa0cCtcZHTg3TjsN2ScsBl1uQNMGod/y+aIC3StuiVpN9HU+6q2rRhjEjrczOqzbNMTBu+25bvMKZlB3TnXMOIRDvjgNZZ4hbIi7A3KnFZmOelJqCqy6uPLysHtECfCD+wZR51Ef20x/2MMVQqFcot2hoYY+jt7a27cEagEkO50vy3UqHPL6yHY2OgWPYl4Rb6DhFhfHy8ZWelTCZDT0/PnPtqTZLGSy1K1wH5bOvUvQAYVcedtsxHgj7K6giWlQMuM9uPFf45KmJUUGkPfIVCgZe97GWccsopPlg+u1VB8reJiQnuueceUqnUjHuMQKEML9sMp7xK6yasqoKEcPg54f7HIZ+ZuXCSVGI945Ww9fiFvUNVqVarnH/++ZMbpdFYDhw4wNNPP00+n58EoYgvy5btgbefrQRN5s8q/PhhoVTx50cagdABWTF8NypwSZijX2RZ3TLLxgG95SvcF1e411bItyF+jTGUSiW2b9/OTTfdxNatW1v+zl/91V/xqU99it7eXpxzGIFSFba/Am76U8vWExLFp8EMRzFc+VnD/75VGMj7FK9aJdb3XaTc8AeuZRHMeu8wxjAxMcHnP/95PvGJT7Qcx+HDh7n00ks5cOAA2WwWVYdzHnzf/qzjvHPUxyelgaWXhrvuFi77A0Mtg75RUfM0cMRZ7rFl3pHKM7qMXNDMbve5VJdTxSjsjUtYbW+HGWMoFotcfvnlbN26lWq1inOu7mWtRVW54oor2LJlC9VqNdEboViCyy9Qtp4I1RFwJV9ldPZVnYBUBq68dKq84/R/Xnmpksr4++o93+gdIkK1WmXLli1cccUVqCrW2oZjqVarbN26lcsvv5xisZj0jfMc+JxtynnnKPFw43G4EsTDcN45yjnblIlSc53RAWmE70RFRp3FLBMmVHV5RLDv9yE8aqvcFZfJi8zL8q19bK2JX6N7RIRKpTL3nloSduQ5QSNbJgDUeg42W7zWygGr9RxxIe+o6bLZbLapIWKMadhjVwRctfk4JoFVbb+QZVaEx1yV+22FN4UZxlX9WJbBKF0W8ZtC+E5cYnwB7L2ertTMWm40ye28QqSJAiSLf8d8xqFNeqK0tbgyPyZhVPhuXKKqMzn/mgWgztIxfmzLZBcQ9ZB5JEk2dF3Q3jGUpofwdPHvmM84GoHVtYkMp/NjElkRfmIr/NRWySU6+lKDcMlFcM3XdHNU4IizC3I8S+1caqIjNVowY0xd1wW1pN+k61ijYubW+c6vtSaYs0GVCkECf18j5tLsHc45enp6Jv2VDQHmHGEY1v3/VcGkIS60AJSDcJ7dNUzipbjNljg1SONqKsWScsDpqdkdvKaUTGXYOv4lLpGZJ/dzzpHL5di9ezeHDx8mnU43bO4cBAEiwo033siRI0dIp9PJQkMuC7v3CoefhPQgmCyY3Nwr3QtRGW64SSa55vR/3nCTEJX9ffWeb/QOVSWdTnPkyBFuvPFGRISgSbPqdDrN4cOH2b17N7lczm88hd4s3P2wcNfdQjjUeBwmC+GQt4LvfljozbbHDW3CBe+MyzzhYjKJ8ahLhBFUkZte/BpdSu7Xj3CzLfM/q6P0IvPmfqvJD1goL94PGEURZ5999qL9gGdt64wfsJ4RNaaO96f7+ECql7EldsksCQB1BosVfrfyAo+7mCyyoKwXYwzVanuRkHy+cSSkGkO52jqKkU3X5xjepyg+EiJ1ZFPyN/8OrfsOEaFQmGgrEpJON46EFMutIyG5zPyLGAgQAZvE8Oc9x9EjU+dKlsI5vWQ6oMNnW9znqosCn+cKjnQ6TRBmWuiKihGHbeRwTXkXSnMQNwAXgBgyaUs6aM7HTRB4ZbFOa1kjSi7fh7YIAwXGoXWeV/X94XKZNhY3mP9ZaQV6gMNqudtVuCTMMLaELpkliYRoMlOxCP8YFRaV61cTO6rK5k3WI1vm/qAYqFTg+TGvK80Wn/4dsHkTTd8xNuFFbb5nJhesqQL5fJ6hTUNNEgWEsbGxyXunczARGCvCi/odPT0N+tolqeJHj/n7Z4tPVRgvwtZN/nvnFAZN/lsdHD7mxfV8E1w0EcXfiQu8xfRgUF94fAm44JJkwzggh/CwrXK/q5JfIPcTgdjCUB/c+PuOM7cpWp3r31K8ZVtS+MPrDX97s9CXVI6azzvUwKER4ao/Mdz3yFRCQS0ic+aZZ3L99ddzwgknTFrm9Rzmhw4d4qqrruK+++6bNCKM8cD58CXKZ65yZAVMnYiQU5A03PuwcMXnDKOFqY6YkqgRn/+E8p5fcUh1sprGzHEoaBq+/l3D714v9Myz2akDsghPuJh/d1XeYNKTGdOdRov84wkn61IAsA/DX0Rj3GJL9C3A+KiJkKMj8OkPKX/4Ow6OJluz8awxcgS2fTig6AswEJh5vMMCm+C2W4VLfscw1FtzqwQMDw9z880387a3va2tb7/tttu45JJLGBoawjmLtR7QD/+tZXALUGrihbXAZvjMfzf80d8Jmwc9gMaK8ObTlduud/75VpSFt11luPMBoT83P3FsgALKG02aT6cHKS/RsYlwKcCXQXjURdxpy+QWCL7p1JcDWwQXN1ZaVf2iinixM1GaibN23mEdmCJk0hCaabFgVcIwJJPJTPoig6A+iq21GGPIZDKEYTgpqp1OiUNX8iCTBoCIrf+Ovtxc315fDlyE5+KmuR9QQiYlwULWMYvwkKvyhIt5hQkp0fmMaTO7nP9iLwekRbjDlZnokAlvk/hr7SB/o8skoKlnfc7nHc7VOdCdOI9rMdxmlzGmbkKpS8pomza+IzD1+wBbN5UU23IssriCTQG+NMo/2yIGodNY8YfTOlzTOQ0c1pgfxAsLu3XUB7QaSRf/fLtLpossj1qTZvfYCrvCmE0IUYcNkY66YWof/C1b4rA6BmTx4hfFK9Ek9Z+bTLaIv9fIwt5hnR9EJt3YN2etJY7jhlawTdhWJpOp60fsSXkRq016gMex5z49qZkAmgwHhj7bxjQRL876Cqr1QoLz2SspYESVf7Fl3hvkqHRYDHdUBwyAcZQf2go9IovmfqreDbHvfvitGDKbaZooQBbu/J5wZJhJy28+7wgVyMBtPxFfHm+aa8Vay2233cZZZ53VUP8DCMNw0gix1iYxbA+EI8Nw9wHhgrerNyIaADBMvMH77p9yw9RKET/wuHD0EGw+MfEYS2PkHH3S35/LzC8xYTZT6RFhb1zmV4MsPYmN1CkuKN/a+mrtFPfrRbjVlfnL6ji9HQBgzRVTKMOv7FDOeZ3P6asXAsN4K/GrNwvD4zP9Z+2+Q0L4xTPwtdtkzuGjmg743ve+l5NOOqlpGO0Xv/gFX/va12bk/NV8kUN98P5LlP6cn7S635GCu/8NvrtfZoTzjPHjOPUkuOytSlBz48zywyhgBb79feGhX/iQ4GIaFxigoMon031cZDKMd5ALdgyA3oMufCYa4acuWlTko57oGi9Btdpk6yUO2P78lN9sIe8wgS/124hGR0dbhtGMMQwMDDT0a44VaN5ZSiGd9nWvXZ1xlKo+y7spG1KfhNEorDhfAJaBkyTgs+nBjur1HXFE18Ju97sqj7qIHFO5ZJ1g1U59OwbJt2Exu/o6z7zeYRtE4kQ47rjj2rTc7Rw9sRZG2zzYnvpRz4KtuXPymfbmbbEtW3RKu+FJjXnYVnmdSVPoEBfsiA7oVRZlty1SQCfBl1XmFElcKMV25d/R6txxu3rtYkFhLctymF8SvbgsoAIllD22xHbTufKgHbGCJXHsvzPI8uuSpUchErg/bXg0NIwYluV8QZc6BzwHZBReESuvrzqGrFI0glGllFjHnVjPjnDAmrl+epAm7+DxtPAP+YBnkoS1XBd8a5Z+LvC8g3cULeeXHYUAqh3swt4xP6BDEac8FArX94UUBHLJh3YrX61dMgovADfkDePqOLfiiMXneXbGD9gBI6RmbFjgG/mQkkCv0i06tA6olh8YKnwrH3JSHLE1VqrSGSPEdCr+m1G4v8fwTChku+BbV+QSXa0q8IOMmSyn14nLdHKn/Cw03Uqn6xiEKYUnQkNROmdUdkwHtMCoWZt9Ao1p/9xwp8xMYe21FjNAwQglgbx2ygru1Kwry1rWq2OTKlAoC3EshOHSFz4XptK9+nJrr9C6AKLaMbdGRzjgkrWGXybwnXlylfddPMEJQxasLFmRUAVUlImq4Z/uzPGde7JkUmuv7Vgn1ztkg1JgYKwoXPj6Mn/ze88TpNVH8JdpCS96U5FX/90Af7pngMFet2E7fYbagZDtWuR+zkE6VH77N8YJAqiOGJ/EsAwizKlgqvDxd0zwrR/mOPh8MO+DQ+uEA2poQDqZ37Um9JjkdNnxg46TtsRoRXyi5zJNggFsDD15x2teEvHzQyHZtNY9z7xeKTn6KaFVN2aQfrcITjh5FHCtDF4hHcBzI4ZfHAnZ/toK1XFZRg4IJgWVguFnz6ToSemiU6aWEzo+0XdRuqt6xqdjocIjociOqs8d2jCM0BioxsKffbOPv/m9CulBt2w6oEEhDV/8uwF+/mxqI+qAGopIRfWRUNF4sfJ89vNrYTNbB31ZZe+/ZXjXp49fMSu4P7f2wNcJHdA/r3EoIvsD5FxtWa2kPfGypgwRhXxGufexNHf/9LiuH3D5AKwBgojsD9VxwBlFF4Gf2m5Yi/HfGghlObtvrtFISG2t3SI5oII4FHUcCBV7X9X3OA4W8ULEKQPOF7ERXVvOVedWYBXX4mYF8g56nOLQxQxFqqqxYu8zo6ZyIFaeTSGyUEO29tArq90cmPVKAsQGTowcOecWLO0UNIVIrDw7aioHzCePHp0Q0dvTRgBdkCtKgLIRtpctJ0SOkqzNuHCXGlntXr1KKZxdjIgSK03nDz5AbdoIInr7J48enTAJa92byHaZbeW0c9XYc0rhP45VySsUxX94rd5j91p7l8Ezkkh8LuA7xmrJqFMGwwJwIgnW9kISC3ZGbi1aVwhEcq79lhozdUCFisDLq5YPHSvzrYE0h1Les7sUdeW6tPQit1Z3sd86LpmIOKsYUzBex5+vr6rWeiRATNG6ggvkVgC5hp3hdeyL/3bwZV/vDYJ3T6iNBVlwkoKDyVNx/54JeDwdMBYY3/6pu65rx9oVoccpJ0aWU8uWQesoiSwqg1nRuFeCcMLaf/jwyNPvuYadYbidfR4XgbkhQt8NYnQBfj2dpi9UEvH7xmLMG0oxrpsnvUa5oO/vVzUyA3y6QGyAmAiFwNwAsJ193vd8DZjrwN049LK9ORPsLKlznbAjlrK6epeWz2MkHVhDBZsVY4rO7rti+OkLapgzAG9lp/Hcy9wQgOjifDwzrKcu+Na+BSyLBHAifglADJ771TAn024017LTnDj0+O05MW8pqrNdb0qXOsRFbU5MUFR3x5PDr7zwWva5WvuRSYBtB/NJnrS/nul/XEQ+ZKc2QJe6tGgMGgFV/dBvlR98YjuYPQlznATY5WB3Q/DhkYN3lNR9pVdMoL63eJe6tBjuF/eKCUrqvvLhkYN37Ibg8mlpAzNE7DaQt4Js6hv6UezcBwKkz3WuylqXNh650Fu+z0kY/MbriqPFo8C+aebFDBF7HbjtIB85+uThyPIB41PjuqVdurQgEnBGkMjygY8cffLwdpDrZuFpjpGxB3QvhO+sjD32q+le6RPzyxXViK5B0qX5UdQrJlVw9rqPjR28cS+El9bJ2GsoWvdCeAHEXxp86Tf7xbxzTF0kvgpbl7rUSu+L+sWkxtT9n4+NHPyNGpbq3dsw5PZW33JW/lrNx4roy3NidhTUxWYZuqx3ac2KXBzEeTGpour+SM3HdKpwWl0yTV6m14JcPfrUcEnl4qrq/ryY0PnmAF3q0lyLA6K8mLCqur+kcvHVo08NX+vTFrQZaFuxUyPgvjDw8qEesbfkJNgx7mwEpJbtIG2XVrnMVYCozwSpotr9FQ0uvnr0qeEadlpxTeYDwgz2ixkxl0+oc4l/puus3tj6nhOgV4wpq9tdJvh4u+BrqgPONqevAXP16FPDwLu+NPCSAymRa5xChMaygWvMbHDwxSkkNAIFddd9bPSZa8Ent7TrvpN5/qCQdBz9Qv9LL06Lfjkj5oSC54bajR1vGOBZAcl7rneoqvKRq8cO3lLLPZZ55LHMS3wm7SLcXgivHjt4S6lqzizivhwiJiMSOIidt57pXuvvcv4kaZwRCULEFHFfLlXNmVePHbxlr29x52SeSVQLtiKmx/S+OPDiCwOV3+8RudACZXW146NGumG8tc7tJtcyI0YCoKJ6uxX93MdHn719NhYW4rpZzMfJHjC1H7+h7yUfBH1/YOSiEKGsDl/sYrIedddgWTMeFZyCBBBkxBCjWKe3gnz1yvFn/r4GvF0L4HodA+B0bjj9Q67vP+HtIfL+GC7LiOkD39wkRtHkYP00zih0ueQKMji/Zjp1GM2ECOnExVZWNx7Ct2P0q1eNHfpePcazGOrows8G4g2bXvJSifRCJ7wZ5QInvCItIgbBejASdw8rrRgJEIogQIDgUKqqapQnEPYa5U5Nye1XHnvmYKeBtyQAnA5E8DmGtb/9/ZYt+WIxOF1EThc4OcKdJyop4DVG6O+mfS0v5zO+msoY8DMVjVKYuxQeVdUHcjn7wAePHCk0W89O0f8HuDOc0cF4LaQAAAAASUVORK5CYII=",
    "admin": "iVBORw0KGgoAAAANSUhEUgAAAKAAAACgCAYAAACLz2ctAAAmhUlEQVR42u2deZRdV3Xmf/uce9/8qkoqzbIlecADlhUwNh7StjBmSsi4Op1OCEmaTocQSJMVSFYnaWggpoMZsjrp7kWygIYQ2kMnJKRDL4JNjIkcG8smWSDbYBsvo8GDppJqeuO955z+49xbelX1XumVVCXVcPdab0kqvXrv3nO+++397bPPPsLimE7+NOkPdu3aVa7Varucc7uAl1lrbwJC4DKl1IBzzgFCZufCnIiItXYceAaIlFIPA98XkX3lcnnfvn37anPN50KZLALwLOAALr300gustbcBNzvnbgUuUkoJgMfbqT8zOz8mItP+tNY64Aci8gDwoFLq/mefffb5DryohQSiLAbwduzY8Qal1Fudcz+llKqmQEvAlr5POq4hY77zxITpnHXMiRKRTkBOiMjfWmv/9/79++9baCDKAvz+1IXs2LHjl5RSbwVeLyJYa1Padsn71JyjkbHhOWW9OcwmLwG0Uiqdm68lQPyLbsRzrgGoU+Bt27btNq317ymlbgMwxjjAiojq9R0djIiIoJRCRAiCIEPIIpq1FmMMzrmUIGa54dlT5SygtNaSfMb9xpiPHDx48P6ZWDhXAAyA+MILL9yitf6wiLxNRDDGxOLvQs8FOq01QRAQhiG5XA6l1BTwlFIZShbT5yZzYIzBGEMURURRRBzHU8CcYw6Mc85prYPkcz5njHnfoUOHXkwxsdgATOM1u2PHjjeKyOeUUpuNMSkN615PnVKKXC5HsVgkl8uhtUZEMjGyBMRHyobtdptWq0Wz2cQYQ2csOBOIgGitlbX2Jefc2/bv339vEmK5+bhkPY9rnvrw7du3f1Ap9RmgmrCe7hbfWWvRWlMqlRgYGKBSqZDL5aZuOgPd0mDEFIhhGFIoFCgWiwRBgLWWOI67uWcFiLU2FpFBEXnr4OCgjI2NPTADKwvGgAqw27ZtW6O1/jOl1M8mrEc34DnnEBHK5TLlchmtdQa4ZcaOqYhsNptMTEwQx3Ev12wBEjb8S2PMOw4ePHgyxcxCAHAKfCJyr9b6OmNMBITpU5ECLgVZoVCgWq0ShuEs4PWhwDJbAozYCURjDLVajVqtNs1tz/h7pLUOjTGPOefe2C8IZT7gU0pdZ4yJRCTsxXoDAwOUSqUsrlthppSi1WoxNjZGFEVd2dA5F2mtQ2tt3yCU04Fz27ZtQx3gi0Uk6Bbr5XI5BgcHyeVyU/I+s5Xnmq21jI2N0Wg0eoEw1loHHSAcTf+rF8N1td27d2v8muGnU7fbC3zFYpG1a9cShmEGvhXunkWENWvWUK1Wu3o4EQmMMZHW+joR+TTgEiz1r4J3794d/OM//mOcqN1f7+V2rbWUy2XWrFmTzc4qs0KhgFKKZrM5K64XEW2tjbTWOwcHB+U73/nO13fv3h0cOHDA9uOCNWAuvPDC1yul7nPOxfgk4ywqLpVKDA0NZay3iuPCWq3G2NhYL3EZi0hgrX3DoUOHvkaXFRPp5pK3b9++wTn3bRHZkJRJqZnMl4IvExoZCGu1GqOjo91iQisi4pw7KiKvOHDgwNHO1E23GFAA65y7Qym10VprZr7HOTclODLwZZaGYeVyuZsnVNZao5Ta6Jy7g1MFDl0ZUAPmggsuuEVr/UDCfLqbElq3bt1UcjmzzFJcjIyM0G63u7ljIyJijLn1+eef39PpijvZzQGBiNyeVLF0VUGDg4MZ+DLraoODgz0LGUREicjtiZ5wM1VwkLDfv9Vavydxvbpb3FepVDLRkVlXctJao5SiXq/PWjt2zhml1EXVavWp8fHxxxPMWdUZFIrI210PatNaZ+DL7LTxYLFYpFAodPWQzjknIm/vxJxKmM5u3br1VhF5TbfYz1pLpVJBa52NcmantWq12i0O1AkAX7N169ZbEwBqtXv3bknk9NuTX5pFcblcjnK5nMV9mfXlitO6zy54sUn1+9sBdu/e7RG3ffv2TcaYZ0WkNFMdW2sZGhqiVCphrc2qWTLry+I45vjx4zPx4hKQ1rXWlx44cOBwkLz59VrrcjfxkVYyp7FfxoKZ9WNBEJDL5Wi1Wp0gFMAopcpxHL8e+EIqQm7tRGgnnRYKhWyj0AxTAlo7lIAIBNqhVLa3dKb1cMOuE3PB+vXrKyJyW/JG3eeHrCoTwKe3HMYKjbbQbGvyoUNrR62pyQeOfM4Saj9W1gmredicc+Tz+anS/hliBBG5bf369ZUgn89fCWzp1hoj3bm2GgHo2c0PSRTDRENhrDBYNlx2QYvrr6hz45V1BouGh58qsfepMk8dynNiQiNAPufIhw7B4ZxgVyEYtdbk83lqtVpngloSrG3J5/NXBtbaVyUFhNPW6VL327HBfGWzXOJOlYCxUG8p2rFCCQwPxNxy9STXXtbgxivr7NjYRpcNGAEHu66q8Y7WCC+NhDz6VIlvPF7me/sLHDwWEhtFLnTkQ0ugwTmwjlXBjs45wjDsph2cUiowxrwqAK7sFf+lv7ySQafE33ZkhFZb0Y6FYt7ysq0tdl3c4OadNa7e0WLjhjZoB20FkWAmAgQHAs4KSjk2D0f85K0n+cnXjFIbDXjiYJ6Hv1diz+MVDh4JGRnXaOUo5S1hkG5HXbnsaK0lDMNumZP0jq+UzZs3P6y1vjHd/d75rrToYCW6VueEViw0WwrEsbZquOLCFjdcUefGy+vsvLiJLhlwAm3BRoJDEHGeLbs+8T72E0AFDnIWtMPUNPuP5Pjm90p865kijz1T4viYxjkhF1oKOYdS/pqcPYs+F0vURkZGprZ3ptgUEWWM+WbQrcw+Tb+shC4FqVtNBUStqYiMEGrHBesirr+yzrWX1bnu8gZbhiPIW4gFWgoz6dfNlZwSIaf7Lp0wqjPg6gqHoJXjkgtaXHJxg7e+SThyNMfj+/M8+ESZfc8VefbFHI2WJjdNyMiKcNUigtaaKIq6VU4HsmXLljERGaCjY1WazR4eHl6WAqST5SIDjbbCWhgsWy6/oMW1lzW46eU1dm5rUV4T+dtuCy4SrPUst5DPnkvY0TlBcKjQQc6BOExd88RzBb75dIlHnipNCRmAQs6RD9zUvSxHV62UYnx8nImJiU5Cc4kYGZctW7a4bsFjoVBgzZo1ywKAqYCQhOVakdBsK8LAsXEo5ocubnLrKyfZdVGTS7a0/eRboK0wsSSg9a713ATnJGDy7EjeQuCgpXhpJGTvU0W+sa/Mdw8UOHg0JDZCPrRTaR/c8mFHpRQTExOMj4939aiyZcuWWVWq1loGBgaoVqtLVgFPExCx0GgrjIWBkmXHpojrr6hz/eUNXnlJg8Gh2AuISEFbMAkTpcA98yg7eZTPssOhtZ4dlXJIyo4OaqOaJw4UeOh7JfY8XubgkZCxmkZrRym3PISMiNBqtThx4kRXMdKVAZciAAUQ5UFnrNCOhGZbEIENQ4aXb29y05V1bt5VY8eG6FSapC3Y+JSAUGcDuA7WEQ3kHSgHLYFIvItV7qzA2FXIKDB1xf4jOR7+XpFvPd0pZCAXuiUrZE4DQJYFACXJzbXailYslPOWzcMRN1zZ4Jara1y9vSNNEiVpEitTAuKsWc4ln5FzHnQO7Lim+WwOW1cUr2ih18a+xLIt0PIgEOE0LTlPD0bnmBIyhAkgjXDkSI59B/I8+HiZfc8VEiGjpoSMVkvDRS97AArQjoVS3nLF9hY3XNHgpivqXH5hi0I12eGXspybO00yL5ZzgugEcIEDI0RHAmr7CtSfLFB7skB0NMDFQrg2pnh5i/LOJuVdTfLb2lBwiZoWnDn1IJ3phfUWMp4dH3+uwDefLnohcyBPPQGjW+oA3Lx585IFoFaOsbrm524Z550/c5zNFQtF4ye2rTBmgQSE4xRjpROrgQlFY3+O+pMFJr9TpPlcjmjEK1SVT+I1AReBayucAV21FHa0Kb28xcCra+S3R6hB44HXStS28+HE2bvqLkKmoXlpUvHJL67jnj0DDJZM4g2WJgCXdJmLiBcYF29qs3lLm+h4iIoCz3LKA/TM6YRTQEjBZMCcCKg/naf2RIHavgKtgzlsSxAFkrcEA7aDJf1LAlChBXE4I9SfylN7vMDI/x0gXB9T3tmkdJVnx3Bj7Jk1SsBoPBDny44+53gqN2kbakqMbN7S5uJNbaJYWOrlm0u+zkoEWpHgEsGh9ZmDLgWNhEDeevC1hNaBkMb380zsLdF4Jk90IsDFoHIOyTuCvJv6XWfmEicJIxcdUrI4K0THAk58tcqJr1YJhw2Fi1tUdjWpXNsgvzlCBq1PCTUVxGeuqtNEuTN+rFrR0gffsgBgZ57vzAREokxDDyYAO6JpPFFk8jtF6k8WaB7IYSaUZ7mcRZWsT/5a6Q2606Znkha4oSOYitWEyX8uMfFoCX2PJbc1onx1k/JV/qXWGH+fqapOkuLzFTJnnV7KALgAaRIFFB0SWmh6Jqo9UaD+3QK17xRoHwlwRpDAoXKOoGqnYqtOAC3oNWmQskXEg7r1gxyNp/OMfGmQ3OaIwqVtqq+qU766Sbg+RorWu+qmV9VnK2SWJAB7bJ9bPktwjlNMEXoGQwGTisZTeerfzTPxaJnmgZB4TIPzAkKV0iWuBHD23Fwr7lSOTvKOoGj9kuHxgNaLIWN7ygSDhsKONuVdTSo7mxQvayFVO7V6Q8SC5BzP6TT1wFOw3BmP0CVMkQiIZ4o+lvt+ntahENtMWC7vCCo2KZ9iahXjvD88ZoarBlxbqD1eYPJfihwrOPLbIoova1G9vk7pMp9zlBBoeFe9nBkxWNbgCxzR4ZDxx3wsV386T3wiwBlQ4QwBca5YbgFcNULC0F7ItA6ENJ7NcfK+KsHamNLlLUpXNRm4rkG4MfJpqWUKwmVbb+WsQNEx+kCF5z+xnolHSpgJjSr5VIkkKxbO0Eev9iVoNmFHl7jqAS+OzIRm4pESz39iPaMPVKCYiKWVGAOe71jQf79NXGX3QZbAEQxadMViY1karnVRXPWp+1UFDzoJet2pJCsnNhnD8x//9cKRWimT487qyLxldr82AeQKuN/sYLbMMgAuayGUNQtbeACKCO12O2vDQc8QC9sUChe1GfjhOrbuV1Eymz+WloEIWXq156IcNtIM3lyjeGmLk1+r4paaEJ02h+dXgFhre2KpJwOm58lm1mVQjRBUDJVXNihe3qJwSQvXkKw5TA8AxnHcs6taT8dhrc26ofYYMdtUlHc2yW2JoOAYuK6ObSdLY5nNAmB69vC8AJiepp2dYD7TOzhcDIM313y1dFuoXttA5Zd3QnixLI7jmZvS+1fBrVYrEyIzxUdbkdsUU35Fw9fwtYXCy1oUL2pjWyrLK8wI5aIomooB+xYhM3/5fIuQJbPDSzlMU1F9bZ1gU4wb9+X5MmgY3F2j9lQeKbqFK+U6m7GbJibPHwBTEus8Y7hvBoyiqGtLhdUbz/g4r3pdw6/RivNxXxvKr2ygq3aquiUzH8a12+05wzh1OgZqNBoZABP361o+91fa1fSlUOnGopYiv61N8eIWtpm5YTh1wHUURafTdHN/SLPZnDOIXDX4Uw7bSgTHoMHFHUNngZxj6NaaX5POnlecc90OrOk/BuxUMc1ms9dhdOckBlwKiWhnBF2xXv220+6pHY9xS6hc0yBcYzAN5Xe+ufOKgPMWA6arH61Wa2oez4gBU6vVaqs7J5jk/kqXtshf1IaZaleAthBsjClf2cQ1V3dSWkT6xozq58OiKKJer6/anGCa+6u+ugE98n3OCWhH9aZ6ss/XrVrwtVotGo1GX3hR/X7oxMTE6owFBWykCIcNAz9cg2b3FQ9RDhpC9bo6uc2RzwmuUhacmJjoO3/cN6UZY2Y2GVw96rcplF/eJNgU++ZD0uN9kUINGSq7mkk3hdXFgulJmc1ms+/MSdAvUlO/nsvlpo7tOgdxNM4mieiONhTnfmQdQ7dN+lZsc9Ba6narr65z4t6Kd8vnXn34h4Fk7Ny5Od0qFR5jY2M9k85dATjfLxobGyMMQ4IgWNrLdH0QtQDMFauJb9ub2xRTenkTTicuFNAQSruaFC5q03ohh8qfRsU76e+xWuIa0DnH6OjovM8TDOaLcmsto6OjDA8PL+kBsTXV0fW6N1mkzYG63q+CeFwx/OZx1LDBjWmfXpnrI2PvhqvXNJj8dpFg0PZu7eGSRpenuUYEVHHpIlBEGBsbo91uz3vRIjiTL2u1WoyNjTE0NLQ0WVC8G0Qcrt0lJydJXq9qKGyPPLtILwEiDL1mEvqM6UQ5aApDr5+E0O9P7kpxzjNm80CImdA9r1FyFpxQe6KwJDchKaWYnJykVqud0YrZvAHonEMpRa1WA5gCYbrgvCREgxFU6Nj63mPIoIGa6nIKno/tCE4TWgpQl97io9v720Juc8SGXzlx+s+OgW5lXAYoW9yY5oU/Wu/BeL6T2x0Y6ATf6OjoVNw3bwY8EwZLv2hychLnHENDQ9MubEFFyHxXQhyIdozuKdP4QY4LfvsYxZ1N3Kg+1Usldc1O+hIK8+7BIkAsuNHTB6IiM68p6XUzZGh8p8jzn1hP61CIrs5zw/Mir4SkJJSCbyY4F40Bu12Ec47BwUGUUkvDJTsIBg3twwEH3r+JTb86wtCbJqCuvLtVp4Aii0UpwmnjxVmgTa5NKobRr1Q5/OlhTEMIBs2SqbJJwZae/XG2Xi9YiCehXq8TxzFDQ0PTDrc+rxg0gi46rIHn/2g9je/n2fRrI55kWmp+4DhH1yt53wXi8P9Yx8jfDaDKFl10Swp81lrGxsYWbGVsQbLKSimiKOL48eNTR3MuhXjQWa9k9YBl5MsDHPj9TcRjGqkaH2MtFTMgVUM8pjnw+5sY+fIAesB3cF0KDZVEBKUU7Xab48ePL+iybLBQLjMNQk+ePEmj0WBgYGDqrOEz/Y40BjyrK0x68ukBS+3JIs+9Zwtb332c8vV1mFAdCcHzEyoAMGip7S3xwn9fR3Q8QA/Ys35AFqoiWik1tQpWr9enROhC4WbB1tXSCxIRms0mx44dY2xsDGPM0mBEA7pkiUc1+z+wkRN/NQhFf5rleUnyWvx3Fy0n/mqQ/R/YSDyq0SV73tk5ZTzwlVDHjh1jcnJyGtEslAWLdQPgF6UbjQbFYpFisTh1duz52vDurG8EKSG8+KfDNA/k2PRrI77bVOPcxYXOCFK02JZw+I/XceIrVc96nF+Xm86bMYZGo0Gj0ZhKLi9WDcCiNqhUSmGtZWJiYmoduVgsks/n0VpP3fA5BWTyNcGQ4cRXqrQOhmz97WPkLoxw43rRQeiMIAOG9qGQFz6xntoTBYKhc69y07FPCcFaS6vVotls0mw2p/byLnbxyTnpkJreRHqDWmuCICAMQ3K5HFrrKUB23rDv9i6LEqI5IwRDhvrTBX7w3i1sfucIA6+dhLGkjEoWAfgOZMgw/vUKL31ymHhcLxr4JAGXf00PldJuBene73a7PfXvNMY7V1VPwbl2hamUT8GYDlIaJ3ae0B5oOD4q1OvRopw74IygyxbTUBy6Yz0bDoWsf8uoX51YyN7LSS9rAjj2+TUcvXMICUGXF2kXnQj1ep3jxyKIHLE5NfZpy5XO3j/pHCxGjLckGLAXEDuFSbp5ubPo1WhoNyGK3aIdfOGM7zoqIRz58zW0DoVs+tUTBJXktE1ZAPBpRzyuOfzptYzeX0EP2jM7f2QeAIzimHbT0GoxBcBu7vd8i8MlVV16ymWceiFCPpT+0hkLkKoZf7iMneixdnympsFOKMYfLnux4RbomuewfOjHruuYLiFb0uXNzkEQwkNPAC2mnfXrN4QL1VfX0QML4MrEn7dWvqpJ7oKo/+KDfoKxtpC7IKJ8VRPbOPtSfWcEPWB9xc+MpkhK/Fg99IQfu6XeWWVJA9BYqJbgyw8J//SYoCr+Z1MT2xDyV7QYurmGqZ1dGiXdeFTe2ey58ejM0z8CeUd5ZxMXn92GJdEOU1MM3Vwjf0XLb5CXU+OlKvBPjwlffkioljrGa4lasNSbDynxR9p/7B74V6+eQR4Ju6z9iXFG95TPigWdFVTBUrq6CfHC7moTcRBD6eomqmDPCtypcFr7E+OzWFoAkrGy1neosRkDnj0LDlTgq3vhwUeZzoJJCXz+0hZDt5wFCwq+9H69PyKL1gLv600OICzsaJNbb3BnqLCn2O+WGvlLW6fag3Sw34OP+rEaqCx99lsWAEznz1r4+D3+HJBZLBh5FjzTtEbadqO8s3mq7UY/H9OvmJCkVH/QUN555jvmprFf1J39Pn6PYO3y2RG6LAB4rliwtLPZ/8yldYWB6z+dMt/vWOHst2wA6JKiYWMcH7t7gVkw3Xg+ZChd1exr74cz4svlI8GMamQgOcnSzc2ytITSVU3CIYON5qeG+2G/j90tGONjv+XSV1TN7Ii/FF/giI1joAL37nU8uHcBWVD86ZT5rRHhOjP3Ckh6Zu+gofF0gR+8bxPPvmcL41+vQMUmbCi944hICNcZ8lsj3DzSPH2x314/NgMViI0fs+Uwt8uqzYEkA/6xe1gwFhTxLrR0VRPmUKjOCBQtTsGxv1jD/v+0mcaz/qT1g3ds4IWPbvDFrgOmJxs6K1CwlK5q+hWYPpV2X+x3jx+b5dYNZFkBMI0F793LgrGgc/7Qv/IPNT2oZ4Kik/WeKbD/dzdx5PNrQDlU0SEB6Irl5P0VnntvwoZl61dSTJd0jIXyDzWRwPW3Iapv9ltesd+yBOCCs2DifnMbYwoXzU6/zGK9391E/ZkCwaA5Bc7kuK5gwJfUH/zIBl78k/XYSKBipx8qmKZjLmqT2xj35YZXMvsB6Fwu98HldMHWQSEP3/sB3Hq1sOMSMOkyXdqnb3NM/GJI7bsFdNFv7O71+LmGovLKBkNvnDzFLslGdRmwNJ4q8PxH13Pya1VU3qFyPVZJnCAadN5Re7LAxKMlcptj8pe0T+39VUAsqCFL48k8zefyU+ca92S/Sc3a100y9ObxafubjQVdgQcfgfd/xlEpLz/2W5YM2MmCH73bnRULivj9EpVrmr6LAnJa1puzYjk5SjUYsLRfDDn4gY0c/p/DXvGWvEBxCIijck3Tq/s54sB+2O+jd7tly37LFoALFQtao9BVS/Gy1lT6ZXasB7o4v9SOM/6Ucyk4jn9pkOfeu5n6k3lkKPaAawnFy1roqsUatSpjv2UNwJQB7NmwoPJ9/4rb2v7ILQ1OnwHrzZWoTjbIt14MOfC+TRz787W4ANCQ2xJR3Nb27XzVmbOftcu7D+ayBaCxUD0LFkyrX0o7m8jGiMZT+bNivbncqCo4UHAkAXfjqTyyMaLUozpmPuxXXcbstyxFyLSnR6DZhiMn4RfeJDCzcl9BblPM2DcqXYSI3yux4S2jjD9Q4flPbCA6HhJUjX/vQq4kJJ+li5b24RyjX6+ggPKVLcYerMymASeonGPLfxwhqNrpldkOJIB3ftzxzCFHPlz6FS8rFoAuVcQH4NarYccl0r8itqCrjsYzeU5+tYoqzKFwF+yCPbAQGH+4TOuFnBcmHemf/pSv4/3/y1Ep+TBkOduyb/icxoJ33DXPvKACWxeaz+UIBvwvnos9uelBNsGApflcDlufHgP2E/vdcRfLPvZbMQA0FqpluPdRx4N73fxiQQHJOQ+Kc+nGknSN5Ka3fesv9nPc+6ijWl7esd+KAWBaKWMN3HHXGSji83qa0fyV7x13+Y5fy6niZS4LVsJ5wLGBStnXwu3Z67jlRsFMglazWXDk76sEA2bJnWopydbN4R+Z8Ow3Pjv22/NNx1f3+lWPdKvlcp++FXPohyTx1R13ukWpml50MuyH/e704cJKOv9mxQDQWM+C9z7q2DPfWHAJsN/pYr89SexXWSGx34oD4LxZ0C4dHnF2dbLfiokBO2PBcgnu2+vY84hwy029Y8FjXxoktzHCxed3SiVwREcD1v3UeO/Y72HHfXst5dLsNhsZAy5BFvR5QTubBRMQbvjlE6x90zjxmD516vn5MA1mXDN4c40Nv3Rymuudrnztisn7rXgAGgvlst8fsecRN7ubQhLsX/D7Rxn+8XHM+WjTK37k45OatW8eZ9vth9Hl6c2QpmK/Rxz37nWUV1jst2IBOC0W7MaCyRke1BSb332cre8+jq0pr4zVuRlxZwRbF7a+6zibf2MEGspfk3RnP2dX7smvKxKAc7JgJ9tNKNb8+DgX/uej6ILFNn1V82KqXRcJSju2/tZx1v7smD+FyU2fidXCfitOhEyXlp4FP3Kn4ZYbgtkJ26RgwY1rBl47QW59zMEPbyA6qdElt+C9+3yqRRNUDds+dMSf3nSye0tgl+wz+cidBmd9yf5KnaYVe/q0sVAqeRZ86FFHMAxR1B0YnNAULmtx8Z+8SOnyFvGoRgK3oOCLJzTFi1ts/8PDFK/oDb4ohmANPPSoZ79SaeWyH4AOw/CDK/XmJOms9e1nHbddI6zbIMRNmNX+WAFtQVUsg7trmDFNbV8BVXQLAD6IxzWVXU22fegIuU0R1BTSpTdtHENYgcNH4Jf/wHD0JATBymU/ACkWiyv6XHmloN6A9YPwlf8W8KpXCdEIhN2aE1sgcJCDI59Zy/EvDUxVM8/7LJHExccnNOt+aozN7xzx+4Qj5c8H6QK+YB38yz87fvJ3Yl44DqXi8q/3W9UMCH4CCzmYaDjuvs+xeUi45jrB1NNO8jNAYwUioXJzjdyQZfyhMihQpzvWdabStQItYeMvn2Tjr5yEyKeAZrX+dRBbCIbgr79i+fn3G46cdJSLgjGL1hp76QAwCIIPssLNOu/KWhH8zdctwwW44VUKFyd1eTKbuagrCjublK9oMfloCTOpUfk59hh3uFwXCxjY8q4Rhn9+NDkSbHaax7nk2obhs//H8tYPxETJA2Msq8JWBQDTyQ4UhDn4uz2Oo8cdP3abQhzY2B9qOIvFmkLu4jaVVzRpPp2ndThEF3qDUDSYmiIoW3b8wWGqN9f8OcWaWYk8a0GFoIrwOx83/N4nDcUiaL3y3e60MSsUCo5VZIKf5Mka/OiNijtvDxhag18z7pIDdLEgFYMZ1xz68EYm9xUIBuysNE1a0ZLfEnPB7xyjcGWz58lLxoAuwGQLfuvjMZ/5sqVUSg9nZFXZqgNgakEAk5Nw407hC7cHXLJNiCf8z2cjRiD0DYde+uQwx/92kGCtOXX6UeCIT2rKO5ts++AR9ICZtploFvgqcHIU3vybEd98wlGteBGyGidC8vn8qgQgeCU8WYP1Q8JX/jjk2tMpZO0V8rG7hzh21xDkHCpI1nR/dJxN7xhBhb7zQTfwxUmO75+/7fiF90c8fdDX90Uxq9ZWTQzYUyHnYaIB99xr2DykuOY61VshO6+QyzfVCQctE3tL2KZi/b8ZY/O7RhCHr+frAr4ohnAIvvktx5vf0+bQEVZkeVXGgGdgSnmAxBH8yXsC3v0LGtvwrKe6ts0AGbLUHi4RHQsY+ukxGNWngNpF6ep1wmfvjPn1j8ZYgVzo3fFqN8nn85aVW2zRPwiT9Euj4XjHTwf86fsDaIFtg9I9XHLBebdcU10XNW3SyFwV4PZPGf7Lp2JyudWndOdKTmQMOMPLKg31eqqQwzkVMp17Tmb+lwGVA/Lw67fH/NmXYopFWZVKd84xz+VyY8CA13MZE6YKuV6HG65SfOHDIZfOpZDprXRHTzre8r6Iv3/EUir65HIGPs98CdbGFfB0xw8zS9RqqQiPPGm56d+1+NbjlmBY+lKrcezB9+xBx4/8ZsTfP2IoFb3YyMA3DYAATyt8A9nMZgLJeBCemITXvavN578YE66TOVksjiEYFr71uAfuI09aSkVZ9Up3rmHWSqldInI9p87+ySyN45I15GYEX3rAsjYv3HhtlzVk591rMCx8/osxb3lfxFgdioUszdJraPFn1HxJK6V2iMiP0TWJkJlzfltnGML/+yfDkaPw46/Tfg25o1m+HhQ+fVfEr/zXiNgJYejBJ9mI9tQfzrk/lyAIrhORh/Hp02y4TqOQm034kRsUd304x9CQQAsowTs/HPGnfx2Tz3tGtFm8d7oY0DjnbhKgEobhk8C2TAn3oZA1NJqO66/S/OUf5hgeFP7D7W3uuT8mn8/SLPNQwAejKLpKfNoh+KyIvC0RJEE2Rv2BcPsmxca1wqPfNRQLmdjoV3jgN8N9Lo7jf68ArLUPZDHg/BRyPi8cOOp49LuWQga++UYzU5hLAbcpCIJngZL4qDkD4mnFiUMpSQ7NcUimNvocNgdQj+P4UuCwTlzuuFLqauBq/NaZLB3Tp0LO4r15mUnE7t9Yaz+PL1L3WWnn3KeSN2Xgy2yxTM3AmlMp4xljHgC+kbjfLKLJbDHYT4BvJFhTwNRBZakY+VQW/2W2mAIkwdgU5macK4RSSt0vIrd0+OvMMluQ2M85t8daext+8cjOjPcEiJVS72f+fQAyy+x0ZhNsxZ3Ep2aiNI7jPcAXEvbLKmUyO1uLEyx9IcGW7tQY0k2lABu01t8GNjCre11mmfXPegnGjhpjXgEc7fj5LAbs/IXDwC8mf8/ccWZnC8BfTDA1C0/dRIbDr9U9m/zCa/GtdTJBktl8LAJC59yHrLWfxS94zErvzZVyCYBYRL4oIv86/cBsXDObB/j+2jn3MymWur1xLgCm/zeklLoXuI6sWiaz/kRHADxmrX0jMNrhWWfZXOIirds6mXzQY8kHR9kYZzYH83WC72SCIXc6lpvL0v6ga0TkXhG5zjkXAWFWAZIZ+MogIBKR0Dn3mHMuBd9pe8v2IyzSNEwD+CJwEbAr+eCsgjqzFAcB8JfOuZ/rF3z9AnAWCMVT360J+GKyPOFqjvfSvUQfcs79BtBkHl2158teaQNbC7xRRD4HbO54CrJUzeqwtLJFAS85594G3Jv82zGPJgdnApiUbr8P3C0ia4Frki+PyVZOVjrwbDL/AnwucbnfpkeebzGtE7y3Af/QgX6bgNF2/Cx7Lc9Xt7n8h2TOz4bIFsRkxpf/EnDfjBuIE3lusslcNi+TzFk84+f3JXPcCbwlIUJnXsgbgL8AxnvcXJz8aTKWPO/sZmbMycz3jCdz+YY5iOesGGyhgWg7gtALEqq+OVHNF2Vpm6Wf1gN+ADwAPAjcDzzfgRe1kLGeLCIjMuNCy0n+cBfwMuAm/NryZWT9Cc8HyCRht2cSd/twIiz3Ja/aaeZzQez/A+tZYJo5+sLWAAAAAElFTkSuQmCC",
    "sale": "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",
    "receipts": "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",
    "live_today": "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",
    "products": "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",
    "folder": "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",
    "reports": "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",
    "expenses": "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",
    "purchases": "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",
    "finance": "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",
    "capital": "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",
    "cloud_sync": "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",
    "license": "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",
    "devices": "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",
    "categories": "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",
    "logo_mark": "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",
}
_ICON_CACHE = {}


def icon_texture(key):
    """Texture for an embedded icon key, or None when unavailable (callers then fall back)."""
    if not key:
        return None
    if key in _ICON_CACHE:
        return _ICON_CACHE[key]
    tex = None
    try:
        b64 = ICON_DATA.get(key)
        if b64:
            import io
            from kivy.core.image import Image as CoreImage
            tex = CoreImage(io.BytesIO(base64.b64decode(b64)), ext="png").texture
    except Exception:
        tex = None
    _ICON_CACHE[key] = tex
    return tex



def wrap_label(text, min_h=0, **kw):
    """Label that wraps to the available width and sizes its own height."""
    kw.setdefault("halign", "left")
    kw.setdefault("valign", "middle")
    kw.setdefault("height", dp(24))
    lab = AppLabel(text=text, size_hint_y=None, **kw)
    lab.bind(width=lambda o, w: setattr(o, "text_size", (w, None)))
    lab.bind(texture_size=lambda o, ts: setattr(o, "height", max(ts[1] + dp(4), min_h)))
    return lab


def _luminance(c):
    return 0.2126 * c[0] + 0.7152 * c[1] + 0.0722 * c[2]


class _Surface(object):
    """Mixin for Button-like widgets: rounded fill, hairline border, soft shadow.

    The caller-facing `background_color` keeps working (including runtime
    changes such as tab highlighting): the value is captured as the fill colour
    and the widget's own rectangular background is kept transparent.
    """

    def _ui_setup(self, fill, radius=10, border=None, shadow=True):
        self._ui_fill = tuple(fill)
        self._ui_rad = dp(radius)
        with self.canvas.before:
            self._ui_sh_c = Color(0.08, 0.14, 0.23, 0.10 if shadow else 0)
            self._ui_sh_r = RoundedRectangle(pos=self.pos, size=self.size, radius=[self._ui_rad])
            self._ui_fill_c = Color(*self._ui_fill)
            self._ui_fill_r = RoundedRectangle(pos=self.pos, size=self.size, radius=[self._ui_rad])
            self._ui_bd_c = Color(*(border if border else (0, 0, 0, 0)))
            self._ui_bd_l = Line(rounded_rectangle=(self.x, self.y, self.width, self.height, self._ui_rad),
                                 width=dp(1))
        self.bind(pos=self._ui_draw, size=self._ui_draw, state=self._ui_draw, disabled=self._ui_draw)
        self.bind(background_color=self._ui_capture)
        self.background_color = (0, 0, 0, 0)
        self._ui_draw()

    def _ui_capture(self, _w, value):
        v = tuple(value)
        if v == (0, 0, 0, 0):
            return
        self._ui_fill = v
        self.background_color = (0, 0, 0, 0)
        self._ui_draw()

    def _ui_draw(self, *_):
        x, y = self.pos
        w, h = self.size
        if w <= 0 or h <= 0:
            return
        r = max(1.0, min(self._ui_rad, w / 2.0, h / 2.0))
        f = self._ui_fill
        if self.disabled:
            rgba = (f[0], f[1], f[2], f[3] * 0.45)
        elif getattr(self, "state", "normal") == "down":
            rgba = (f[0] * 0.82, f[1] * 0.82, f[2] * 0.82, f[3])
        else:
            rgba = f
        self._ui_fill_c.rgba = rgba
        self._ui_fill_r.pos = (x, y)
        self._ui_fill_r.size = (w, h)
        self._ui_fill_r.radius = [r]
        self._ui_sh_r.pos = (x, y - dp(1.5))
        self._ui_sh_r.size = (w, h)
        self._ui_sh_r.radius = [r]
        self._ui_bd_l.rounded_rectangle = (x, y, w, h, r)


class AppButton(_Surface, _FitText, Button):
    def __init__(self, **kwargs):
        text = str(kwargs.get("text", "")).lower()
        flat = kwargs.pop("flat", False)
        radius = kwargs.pop("radius", 10)
        fill = kwargs.pop("background_color", None)
        if fill is None:
            if any(k in text for k in ("cancel", "close")):
                fill = SLATE
            elif any(k in text for k in ("delete", "revoke", "remove", "reject")):
                fill = DANGER
            elif any(k in text for k in ("save", "complete sale", "approve", "activate", "generate code", "join business")):
                fill = SUCCESS
            elif any(k in text for k in ("refresh", "sync", "check online", "copy", "print", "share")):
                fill = INFO
            elif any(k in text for k in ("request", "new business", "join existing")):
                fill = ACCENT
            else:
                fill = PRIMARY
        fill = tuple(fill)
        if len(fill) == 3:
            fill = fill + (1,)
        if "color" not in kwargs:
            # light fills (teal, pale tabs) get dark text for contrast
            kwargs["color"] = PRIMARY if (fill[3] >= 0.9 and _luminance(fill) > 0.55) else (1, 1, 1, 1)
        kwargs.setdefault("background_normal", "")
        kwargs.setdefault("background_down", "")
        kwargs.setdefault("background_disabled_normal", "")
        kwargs.setdefault("background_disabled_down", "")
        kwargs.setdefault("font_name", "Roboto")
        kwargs.setdefault("bold", True)
        kwargs.setdefault("font_size", sp(14))
        super().__init__(**kwargs)
        self._ui_setup(fill, radius=radius, shadow=not flat)
        self._fit_setup()


def clear_selection_artifacts(root=None):
    """Remove any stray selection bubble / handles and clear selections (safe to call anywhere)."""
    try:
        from kivy.core.window import Window as _Win
        for w in list(_Win.children):
            if type(w).__name__ in ("Selector", "TextInputCutCopyPaste", "TextInputHandle", "_SelectionHandle"):
                _Win.remove_widget(w)
    except Exception:
        pass
    try:
        stack = [root] if root is not None else []
        while stack:
            w = stack.pop()
            if isinstance(w, TextInput):
                try:
                    w.cancel_selection()
                except Exception:
                    pass
            stack.extend(getattr(w, "children", []) or [])
    except Exception:
        pass


class AppTextInput(TextInput):
    def __init__(self, **kwargs):
        kwargs.setdefault("background_normal", "")
        kwargs.setdefault("background_active", "")
        kwargs.setdefault("background_color", (1, 1, 1, 1))
        kwargs.setdefault("foreground_color", TEXT_DARK)
        kwargs.setdefault("hint_text_color", (0.45, 0.50, 0.58, 1))
        kwargs.setdefault("cursor_color", ACCENT)
        kwargs.setdefault("selection_color", (ACCENT[0], ACCENT[1], ACCENT[2], 0.35))
        # Kivy draws the select-all bubble and the drag dots on the WINDOW, so they used to stay on top of
        # every other screen. Switch them off for the whole app.
        kwargs["use_bubble"] = False
        kwargs["use_handles"] = False
        kwargs.setdefault("font_name", "Roboto")
        kwargs.setdefault("padding", (dp(12), dp(10)))
        super().__init__(**kwargs)
        with self.canvas.after:
            self._ui_bd_c = Color(*FIELD_BORDER)
            self._ui_bd_l = Line(rounded_rectangle=(self.x, self.y, self.width, self.height, dp(8)), width=dp(1))
        self.bind(pos=self._ui_border, size=self._ui_border, focus=self._ui_border)

    def _ui_border(self, *_):
        w, h = self.size
        if w <= 0 or h <= 0:
            return
        self._ui_bd_c.rgba = ACCENT if self.focus else FIELD_BORDER
        self._ui_bd_l.width = dp(1.6) if self.focus else dp(1)
        self._ui_bd_l.rounded_rectangle = (self.x, self.y, w, h, min(dp(8), h / 2.0))


class AppSpinnerOption(SpinnerOption):
    def __init__(self, **kwargs):
        kwargs.setdefault("background_normal", "")
        kwargs.setdefault("background_down", "")
        kwargs.setdefault("background_color", (1, 1, 1, 1))
        kwargs.setdefault("color", TEXT_DARK)
        kwargs.setdefault("font_size", sp(15))
        kwargs.setdefault("height", dp(46))
        super().__init__(**kwargs)


class AppSpinner(_Surface, _FitText, Spinner):
    def __init__(self, **kwargs):
        fill = kwargs.pop("background_color", CARD_BG)
        kwargs.setdefault("background_normal", "")
        kwargs.setdefault("background_down", "")
        kwargs.setdefault("background_disabled_normal", "")
        kwargs.setdefault("background_disabled_down", "")
        kwargs.setdefault("color", TEXT_DARK)
        kwargs.setdefault("bold", True)
        kwargs.setdefault("option_cls", AppSpinnerOption)
        super().__init__(**kwargs)
        self._ui_setup(fill, radius=10, border=FIELD_BORDER, shadow=False)
        self._fit_setup()


class Card(BoxLayout):
    """White rounded surface with a hairline border and a restrained shadow."""
    def __init__(self, fill=None, border=None, radius=14, shadow=True, **kwargs):
        super().__init__(**kwargs)
        fill = CARD_BG if fill is None else fill
        self._ui_base_fill = tuple(fill)
        self._ui_rad = dp(radius)
        with self.canvas.before:
            self._ui_sh_c = Color(0.08, 0.14, 0.23, 0.07 if shadow else 0)
            self._ui_sh_r = RoundedRectangle(pos=self.pos, size=self.size, radius=[self._ui_rad])
            self._ui_bg_c = Color(*self._ui_base_fill)
            self._ui_bg_r = RoundedRectangle(pos=self.pos, size=self.size, radius=[self._ui_rad])
            self._ui_bd_c = Color(*(CARD_BORDER if border is None else border))
            self._ui_bd_l = Line(rounded_rectangle=(self.x, self.y, self.width, self.height, self._ui_rad),
                                 width=dp(1))
        self.bind(pos=self._ui_card_draw, size=self._ui_card_draw)

    def _ui_card_draw(self, *_):
        x, y = self.pos
        w, h = self.size
        if w <= 0 or h <= 0:
            return
        r = max(1.0, min(self._ui_rad, w / 2.0, h / 2.0))
        self._ui_sh_r.pos = (x, y - dp(2))
        self._ui_sh_r.size = (w, h)
        self._ui_sh_r.radius = [r]
        self._ui_bg_r.pos = (x, y)
        self._ui_bg_r.size = (w, h)
        self._ui_bg_r.radius = [r]
        self._ui_bd_l.rounded_rectangle = (x, y, w, h, r)


class ActionCard(ButtonBehavior, Card):
    """A tappable Card (ripple-style press feedback: the surface darkens while pressed)."""
    def on_state(self, _inst, value):
        base = getattr(self, "_ui_base_fill", None)
        if base is None:
            return
        if value == "down":
            self._ui_bg_c.rgba = (base[0] * 0.93, base[1] * 0.93, base[2] * 0.93, base[3])
        else:
            self._ui_bg_c.rgba = base


class Badge(Card):
    """Icon tile. Uses the embedded colourful icon for icon_key; otherwise a tinted monogram."""
    def __init__(self, text, accent=PRIMARY, size_dp=44, icon_key=None, **kwargs):
        kwargs.setdefault("size_hint", (None, None))
        kwargs["size"] = (dp(size_dp), dp(size_dp))
        tex = icon_texture(icon_key)
        if tex is not None:
            super().__init__(fill=(0, 0, 0, 0), border=(0, 0, 0, 0), radius=12, shadow=False, **kwargs)
            self.add_widget(Image(texture=tex))
            return
        super().__init__(fill=(accent[0], accent[1], accent[2], 0.16), border=(0, 0, 0, 0),
                         radius=12, shadow=False, **kwargs)
        glyph = ICON_GLYPHS.get(icon_key) if (ICON_FONT and icon_key and os.path.exists(str(ICON_FONT))) else None
        self.add_widget(AppLabel(
            text=glyph or str(text),
            font_name=ICON_FONT if glyph else "Roboto",
            font_size=sp(22) if glyph else sp(15 if len(str(text)) < 3 else 13),
            bold=not glyph, color=PRIMARY, halign="center", valign="middle"))


def hero_card(eyebrow, title, subtitle="", logo=None):
    """Navy header card used at the top of the main dashboards (optional logo tile)."""
    card = Card(fill=PRIMARY, border=PRIMARY, radius=18, orientation="vertical",
                size_hint_y=None, padding=(dp(18), dp(16)), spacing=dp(4))
    card.bind(minimum_height=card.setter("height"))
    _logo_tex = icon_texture("logo_mark") if logo else None
    has_logo = _logo_tex is not None
    if has_logo:
        texts = BoxLayout(orientation="vertical", size_hint_y=None, spacing=dp(4))
        texts.bind(minimum_height=texts.setter("height"))
        target = texts
    else:
        target = card
    target.add_widget(wrap_label(str(eyebrow).upper(), font_size=sp(11), bold=True, color=ACCENT))
    target.add_widget(wrap_label(str(title), font_size=sp(24), bold=True, color=(1, 1, 1, 1), min_h=dp(34)))
    if subtitle:
        target.add_widget(wrap_label(subtitle, font_size=sp(13), color=HERO_SUB))
    if has_logo:
        row = BoxLayout(orientation="horizontal", size_hint_y=None, spacing=dp(12), height=dp(72))
        texts.bind(height=lambda i, h: setattr(row, "height", max(h, dp(72))))
        row.add_widget(texts)
        tile = Card(fill=(1, 1, 1, 1), border=(0, 0, 0, 0), radius=14, shadow=False,
                    size_hint=(None, None), size=(dp(64), dp(64)), padding=dp(10),
                    pos_hint={"center_y": .5})
        tile.add_widget(Image(texture=_logo_tex))
        row.add_widget(tile)
        card.add_widget(row)
    return card


def role_card(badge, icon_key, title, subtitle, accent, height=104):
    """Large tappable card: badge | title + description | chevron."""
    card = ActionCard(orientation="horizontal", size_hint_y=None, height=dp(height),
                      padding=dp(14), spacing=dp(14))
    card.add_widget(Badge(badge, accent=accent, icon_key=icon_key, size_dp=56, pos_hint={"center_y": .5}))
    texts = BoxLayout(orientation="vertical", spacing=dp(2))
    t = AppLabel(text=title, bold=True, font_size=sp(18), halign="left", valign="bottom")
    t.bind(size=lambda i, v: setattr(i, "text_size", (v[0], v[1])))
    d = AppLabel(text=subtitle, font_size=sp(12), halign="left", valign="top", color=TEXT_MUTED)
    d.bind(size=lambda i, v: setattr(i, "text_size", (v[0], v[1])))
    texts.add_widget(t)
    texts.add_widget(d)
    card.add_widget(texts)
    card.add_widget(AppLabel(text="\u203a", font_size=sp(28), color=GREY, size_hint_x=None, width=dp(20)))
    return card


class ChoicePicker(BoxLayout):
    """Drop-down list with a real 'type your own' box.

    Picking Custom / Other / Other / Custom reveals a text box right under the
    list and opens the keyboard in it. `.text` always holds the final value
    (what was chosen, or what was typed), so it can be used like a Spinner.
    """
    text = StringProperty("")
    values = ObjectProperty([])
    TRIGGERS = ("custom", "other / custom", "other")

    def __init__(self, text="", values=(), hint="Type your own here", **kwargs):
        super().__init__(orientation="vertical", size_hint_y=None, spacing=dp(4), **kwargs)
        self.bind(minimum_height=self.setter("height"))
        self._lock = False
        self.spinner = AppSpinner(text="", values=[], size_hint_y=None, height=dp(42))
        self.entry = AppTextInput(hint_text=hint, multiline=False, size_hint_y=None, height=0,
                                  opacity=0, disabled=True)
        self.add_widget(self.spinner)
        self.add_widget(self.entry)
        self.spinner.bind(text=self._picked)
        self.entry.bind(text=self._typed)
        self.values = list(values)
        self.text = str(text)
        self._apply_text(self.text)

    def _is_trigger(self, value):
        return str(value or "").strip().casefold() in self.TRIGGERS

    def _show_entry(self, show):
        self.entry.height = dp(44) if show else 0
        self.entry.opacity = 1 if show else 0
        self.entry.disabled = not show
        if not show:
            self.entry.text = ""
            self.entry.focus = False

    def on_values(self, _inst, value):
        if hasattr(self, "spinner"):
            self.spinner.values = list(value or [])

    def on_text(self, _inst, value):
        if getattr(self, "_lock", True) or not hasattr(self, "spinner"):
            return
        self._apply_text(value)

    def _apply_text(self, value):
        """Programmatic change (e.g. selecting an existing product)."""
        self._lock = True
        try:
            value = str(value or "")
            vals = list(self.values or [])
            if value and value not in vals:
                insert_at = len(vals)
                for i, v in enumerate(vals):
                    if self._is_trigger(v):
                        insert_at = i
                        break
                vals.insert(insert_at, value)
                self.values = vals
            self.spinner.text = value
            self._show_entry(False)
        finally:
            self._lock = False

    def _picked(self, _spinner, value):
        if self._lock:
            return
        self._lock = True
        try:
            if self._is_trigger(value):
                self._show_entry(True)
                self.text = "Other" if str(value).strip().casefold() == "other" else ""
                Clock.schedule_once(self._focus_entry, 0.25)
            else:
                self._show_entry(False)
                self.text = str(value)
        finally:
            self._lock = False

    def _focus_entry(self, *_):
        if not self.entry.disabled:
            self.entry.focus = True

    def _typed(self, _entry, value):
        if self._lock:
            return
        self._lock = True
        try:
            typed = str(value or "").strip()
            if typed:
                self.text = typed
            else:
                st = str(self.spinner.text or "").strip().casefold()
                self.text = "Other" if st == "other" else ""
        finally:
            self._lock = False


class FileRow(ButtonBehavior, BoxLayout):
    """A phone-style file/folder row. Tap = open, long-press = start selecting."""
    def __init__(self, icon, title, subtitle="", accent=PRIMARY, selected=False,
                 show_check=False, on_tap=None, on_long=None, **kwargs):
        super().__init__(orientation="horizontal", size_hint_y=None, height=dp(64),
                         padding=(dp(14), dp(8)), spacing=dp(10), **kwargs)
        self._on_tap = on_tap
        self._on_long = on_long
        self._long_fired = False
        self._ev = None
        with self.canvas.before:
            Color(0.08, 0.14, 0.23, 0.05)
            self._shadow = RoundedRectangle(pos=self.pos, size=self.size, radius=[dp(12)])
            Color(*(SELECT_BG if selected else CARD_BG))
            self._bg = RoundedRectangle(pos=self.pos, size=self.size, radius=[dp(12)])
            Color(*(ACCENT if selected else CARD_BORDER))
            self._border = Line(rounded_rectangle=(self.x, self.y, self.width, self.height, dp(12)), width=dp(1))
            Color(*accent)
            self._stripe = RoundedRectangle(pos=self.pos, size=(dp(4), self.height), radius=[dp(2)])
        self.bind(pos=self._redraw, size=self._redraw)
        if show_check:
            box = AppLabel(text=("☑" if selected else "☐"), font_size=sp(26), size_hint_x=None,
                           width=dp(34), color=PRIMARY if selected else GREY)
            self.add_widget(box)
        self.add_widget(Badge((str(title).strip()[:1] or "?").upper(), accent=accent, size_dp=44,
                              icon_key="folder", pos_hint={"center_y": .5}))
        texts = BoxLayout(orientation="vertical")
        t = AppLabel(text=title, bold=True, font_size=sp(15), halign="left", valign="bottom", shorten=True, shorten_from="right")
        t.bind(size=lambda i, v: setattr(i, "text_size", (v[0], v[1])))
        texts.add_widget(t)
        if subtitle:
            sub = AppLabel(text=subtitle, font_size=sp(11), halign="left", valign="top", color=TEXT_MUTED)
            sub.bind(size=lambda i, v: setattr(i, "text_size", (v[0], v[1])))
            texts.add_widget(sub)
        self.add_widget(texts)
        if not show_check:
            self.add_widget(AppLabel(text="›", font_size=sp(26), size_hint_x=None, width=dp(24), color=GREY))

    def _redraw(self, *_):
        x, y = self.pos
        w, h = self.size
        self._shadow.pos = (x, y - dp(1.5))
        self._shadow.size = (w, h)
        self._bg.pos = self.pos
        self._bg.size = self.size
        if w > 0 and h > 0:
            self._border.rounded_rectangle = (x, y, w, h, min(dp(12), h / 2.0))
        self._stripe.pos = (x + dp(1), y + dp(10))
        self._stripe.size = (dp(4), max(h - dp(20), 0))

    def on_touch_down(self, touch):
        if self.collide_point(*touch.pos):
            self._long_fired = False
            if self._ev:
                self._ev.cancel()
            self._ev = Clock.schedule_once(self._long, 0.6)
        return super().on_touch_down(touch)

    def on_touch_up(self, touch):
        if self._ev:
            self._ev.cancel()
            self._ev = None
        return super().on_touch_up(touch)

    def _long(self, *_):
        self._ev = None
        self._long_fired = True
        if self._on_long:
            self._on_long()

    def on_release(self):
        if self._long_fired:
            self._long_fired = False
            return
        if self._on_tap:
            self._on_tap()


def time_text(value):
    when = parse_record_datetime(value)
    return when.strftime("%H:%M") if when else "--:--"


def fmt_day(day):
    return day.strftime("%a %d %b %Y")


def fmt_stamp(when):
    return when.strftime("%a %d %b %Y at %H:%M") if when else "date/time not recorded"


def week_start(day):
    return day - timedelta(days=day.weekday())


def month_start(day):
    return day.replace(day=1)


def completed_weeks(db, today=None):
    """Start dates (Mondays) of weeks that have ENDED and have records, newest first.
    The week still running is never included."""
    current = week_start(today or today_date())
    found = set()
    for record in list(db.sales) + list(db.expenses):
        d = record_date(record.get("date"))
        if d and week_start(d) < current:
            found.add(week_start(d))
    return sorted(found, reverse=True)


def completed_months(db, today=None):
    """First days of months that have ENDED and have records, newest first.
    The month still running is never included."""
    current = month_start(today or today_date())
    found = set()
    for record in list(db.sales) + list(db.expenses):
        d = record_date(record.get("date"))
        if d and month_start(d) < current:
            found.add(month_start(d))
    return sorted(found, reverse=True)


def week_label(start):
    return f"{start.strftime('%d %b %Y')} to {(start + timedelta(days=6)).strftime('%d %b %Y')}"


def month_label(start):
    return start.strftime("%B %Y")


def num(value):
    """Money for tables: 5,000 (no .00 when whole), 576,666.67 when there are cents."""
    v = safe_float(value)
    if CURRENCY["decimals"] == 0 or abs(v - round(v)) < 0.005:
        return f"{int(round(v)):,}"
    return f"{v:,.2f}"


def short_stamp(value):
    """16/09 21:32"""
    when = value if isinstance(value, datetime) else parse_record_datetime(value)
    return when.strftime("%d/%m %H:%M") if when else "--/-- --:--"


def _lr(left, right, width):
    """Label on the left, value on the right. If both cannot share one line, the label wraps onto as many lines
    as it needs (every word kept) and the value is right-aligned on the last line."""
    gap = width - len(left) - len(right)
    if gap >= 1:
        return left + " " * gap + right
    import textwrap
    lines = textwrap.wrap(left, width, subsequent_indent="  ", break_long_words=True) or [""]
    if len(lines[-1]) + 1 + len(right) <= width:
        lines[-1] = lines[-1] + " " * (width - len(lines[-1]) - len(right)) + right
    else:
        lines.append(" " * max(0, width - len(right)) + right)
    return "\n".join(lines)


def _wrap_report(text, width):
    """Wrap any report line wider than the phone-safe width; indentation is kept and no word is dropped."""
    import textwrap
    out = []
    for line in str(text).split("\n"):
        if len(line) <= width:
            out.append(line)
            continue
        lead = len(line) - len(line.lstrip(" "))
        out += textwrap.wrap(line.strip(" "), width, initial_indent=" " * lead, subsequent_indent=" " * (lead + 2),
                             break_long_words=True) or [line]
    return "\n".join(out)


def fmt_row(cells, widths, aligns, wrap=None):
    """One table row (list of lines). The `wrap` column continues on extra lines if too long."""
    cells = [str(c) for c in cells]
    parts = None
    if wrap is not None:
        parts = textwrap.wrap(cells[wrap], widths[wrap]) or [""]
        cells[wrap] = parts[0]

    def one(cs):
        out = []
        for c, w, a in zip(cs, widths, aligns):
            out.append(c.ljust(w) if a == "l" else c.rjust(w))
        return " ".join(out).rstrip()

    lines = [one(cells)]
    if parts:
        for extra in parts[1:]:
            blank = [""] * len(cells)
            blank[wrap] = extra
            lines.append(one(blank))
    return lines


def cap(text):
    text = str(text or "").strip()
    return text[:1].upper() + text[1:]


STATEMENT_WIDTH = 48
RECEIPT_WIDTH = 40


def _naive_dt(value):
    d = parse_record_datetime(value)
    if d is not None and d.tzinfo is not None:
        d = d.astimezone().replace(tzinfo=None)
    return d


def service_recovery_summary(db, sales=None, as_of=None):
    """Service stock recovery: stock moved to services is NOT a loss. Service income first pays back
    the cost of that stock; only income above it is service profit. Pure read-only report.

    as_of: a date (exclusive upper bound, i.e. the day AFTER the period's last day). When given and
    in the past, the stock-transfer figures are rebuilt as they stood at the end of that period, so an
    old statement no longer shows today's live numbers. None (or a future date) = live figures."""
    transfers = list((getattr(db, "settings", {}) or {}).get("service_stock_transfers", []) or [])
    pool_all = getattr(db, "sales", []) or []
    cutoff = None
    if as_of is not None:
        try:
            cutoff = datetime(as_of.year, as_of.month, as_of.day)
        except Exception:
            cutoff = None
    historical = cutoff is not None and cutoff <= datetime.now()

    remaining_by_idx = {}
    if historical:
        # Replay history up to the cutoff: service income pays back the OLDEST transferred stock first,
        # exactly as it was allocated when each service was recorded.
        events = []
        for i, t in enumerate(transfers):
            d = _naive_dt(t.get("date"))
            if d is not None and d < cutoff:
                events.append((d, 0, i, 0.0))
        for x in pool_all:
            if str(x.get("sale_type")) != "non_stock":
                continue
            d = _naive_dt(x.get("date"))
            take = max(0.0, safe_float(x.get("service_stock_cost_allocated")))
            if d is not None and d < cutoff and take > 0:
                events.append((d, 1, -1, take))
        events.sort(key=lambda e: (e[0], e[1]))
        live = {}                                   # transfer index -> remaining cost so far
        order = []                                  # transfer indexes in the order they were added
        for d, kind, i, take in events:
            if kind == 0:
                live[i] = max(0.0, safe_float(transfers[i].get("original_cost"))); order.append(i)
            else:
                left = take
                for j in order:
                    if left <= 0.004:
                        break
                    use = min(live[j], left)
                    live[j] -= use; left -= use
        remaining_by_idx = live

    rows, moved, recovered = [], 0.0, 0.0
    for i, t in enumerate(transfers):
        if historical and i not in remaining_by_idx:
            continue                                # not yet transferred at the end of that period
        orig = max(0.0, safe_float(t.get("original_cost")))
        rem = remaining_by_idx[i] if historical else max(0.0, safe_float(t.get("remaining_cost")))
        rem = min(orig, max(0.0, rem))
        got = max(0.0, orig - rem)
        moved += orig; recovered += got
        rows.append({"product": str(t.get("product", "Item")), "qty": safe_float(t.get("qty")),
                     "unit": str(t.get("unit", "")), "cost": orig, "recovered": got, "remaining": rem,
                     "date": str(t.get("date", ""))[:10]})
    pool = sales if sales is not None else pool_all
    svc = [x for x in pool if str(x.get("sale_type")) == "non_stock"]
    income = sum(safe_float(x.get("total")) for x in svc)
    cost_back = sum(safe_float(x.get("service_stock_cost_allocated")) for x in svc)
    return {"rows": rows, "moved": moved, "recovered": recovered, "remaining": max(0.0, moved - recovered),
            "service_income": income, "service_cost_covered": cost_back, "service_profit": income - cost_back}


def service_recovery_lines(sr, W=36, period_only=False):
    """Plain-text block that explains, in words, why service profit may be 0 for now."""
    if not sr or (not sr["rows"] and sr["service_income"] <= 0):
        return []
    rule = "-" * W
    out = ["", "SERVICE STOCK RECOVERY", rule]
    if not period_only:
        for r in sr["rows"]:
            tag = "COVERED" if r["remaining"] < 0.005 else "still to cover " + num(r["remaining"])
            out.append(_lr("%s x%g" % (r["product"][:16], r["qty"]), num(r["cost"]), W))
            out.append("   recovered %s, %s" % (num(r["recovered"]), tag))
    out += [_lr("Stock moved to services (cost)", num(sr["moved"]), W),
            _lr("Service income received", num(sr["service_income"]), W),
            _lr("- Used to cover stock cost", num(sr["service_cost_covered"]), W),
            _lr("= SERVICE PROFIT", num(sr["service_profit"]), W),
            _lr("Stock cost still to cover", num(sr["remaining"]), W), rule]
    if sr["remaining"] > 0.004:
        out += ["Not a loss: transferred stock is still", "an asset. Service income goes first to",
                "pay back its cost. Profit shows only", "after the full cost is covered."]
    else:
        out += ["All transferred stock cost is covered.", "New service income is now profit."]
    return out


def build_statement_text(shop, kind, start, end, sales, expenses, purchases,
                          capital_start, capital_end, settled_at=None, capital_inventory=None, capital_cash=None, fin=None, shop_db=None):
    """Compact table statement covering everything the owner needs to see at a
    glance: what sold, what stock was bought, what was spent, and how the
    business's capital (net worth) moved over the period."""
    W = STATEMENT_WIDTH
    rule = "-" * W
    last = start if kind == "daily" else end - timedelta(days=1)
    title = {"daily": "DAILY STATEMENT", "weekly": "WEEKLY STATEMENT", "monthly": "MONTHLY STATEMENT"}[kind]
    gross_sales, gross_profit, expenses_total, net_profit = calculate_totals(sales, expenses)
    cost_of_sales = gross_sales - gross_profit
    stock_bought = sum(safe_float(p.get("total_cost", 0)) for p in purchases)
    units = sum(safe_float(s.get("qty", 0)) for s in sales)
    orders = len(group_orders(sales))
    capital_change = capital_end - capital_start
    if capital_inventory is None:
        capital_inventory = 0.0
    if capital_cash is None:
        capital_cash = capital_end - capital_inventory

    out = [shop.upper(), title]
    if kind == "daily":
        out.append(f"Date: {start.strftime('%d/%m/%Y')}" + ("  (today, still open)" if start == today_date() else ""))
    else:
        out.append(f"From: {start.strftime('%d/%m/%Y')}   To: {last.strftime('%d/%m/%Y')}")
        stamp = str(settled_at or "")[:16]
        if stamp:
            when = parse_record_datetime(stamp)
            out.append("Settled: " + (when.strftime("%d/%m/%Y %H:%M") if when else stamp))
        else:
            out.append("Settled" if kind != "daily" else "")

    if fin is not None:
        f, pp = fin["period"], fin["position"]
        okk = fin["setup_done"]
        nd = lambda v: num(v) if okk else "not set"
        out += ["", "SUMMARY FOR THIS PERIOD", rule,
                _lr("Gross sales", num(f["gross_sales"]), W), _lr("- Discounts", num(f["discounts"]), W),
                _lr("- Sales returns", num(f["returns"]), W), _lr("Net sales", num(f["net_sales"]), W),
                _lr("Cost of goods sold", num(f["cogs"]), W),
                _lr("  incl. service stock cost allocated", num(sum(safe_float(x.get("service_stock_cost_allocated")) for x in sales)), W),
                _lr("Gross profit", num(f["gross_profit"]), W),
                _lr("Operating expenses", num(f["operating_expenses"]), W), _lr("Other costs", num(f["other_costs"]), W),
                rule, _lr("NET PROFIT", num(f["net_profit"]), W), rule,
                _lr("Stock purchased", num(f["stock_purchased"]), W), _lr("  paid now", num(f["stock_purchased_paid"]), W),
                _lr("  on credit", num(f["stock_purchased_credit"]), W),
                _lr("Owner investments", num(f["owner_investments"]), W), _lr("Owner withdrawals", num(f["owner_withdrawals"]), W),
                _lr("Orders", str(orders), W), _lr("Units sold", f"{units:g}", W)]
        out += service_recovery_lines(service_recovery_summary(
            shop_db, sales, as_of=(start + timedelta(days=1) if kind == "daily" else end)) if shop_db is not None else None, W)
        out += ["", "POSITION AT END OF PERIOD", rule,
                _lr("Inventory at cost", num(pp["inventory"]), W), _lr("Cash", nd(pp["cash"]), W),
                _lr("Customers owe us", num(pp["receivables"]), W), _lr("Equipment / other assets", num(pp["equipment"] + pp["other_assets"]), W),
                _lr("TOTAL ASSETS", nd(pp["total_assets"]), W), _lr("We owe suppliers", num(pp["payables"]), W),
                _lr("TOTAL LIABILITIES", num(pp["total_liabilities"]), W), rule,
                _lr("NET BUSINESS CAPITAL", nd(pp["net_capital"]) if okk else num(pp["ending_equity"]) + " est", W),
                _lr("WORKING CAPITAL", nd(pp["working_capital"]), W),
                _lr("Capital at start of period", num(capital_start), W), _lr("Capital at end of period", num(capital_end), W)]
    else:
        # ---------------------------------------------------------- SUMMARY
        out += ["", "SUMMARY", rule,
                _lr("Gross sales", num(gross_sales), W),
                _lr("Cost of sales", num(cost_of_sales), W),
                _lr("Gross profit", num(gross_profit), W),
                _lr("Stock purchased", num(stock_bought), W),
                _lr("Expenses", num(expenses_total), W),
                rule,
                _lr("NET PROFIT", num(net_profit), W),
                rule,
                _lr("Orders", str(orders), W),
                _lr("Units sold", f"{units:g}", W)]

        # ---------------------------------------------------------- CAPITAL
        out += ["", "CAPITAL (BUSINESS NET WORTH)", rule,
                _lr("Capital at start", num(capital_start), W),
                _lr("Capital at end (total)", num(capital_end), W),
                _lr("Capital in unsold stock", num(capital_inventory), W),
                _lr("Capital in cash / other", num(capital_cash), W),
                _lr(("Grew by" if capital_change >= 0 else "Fell by"), num(abs(capital_change)), W),
                rule,
                _lr("TOTAL CAPITAL NOW", num(capital_end), W)]

    # ---------------------------------------------------------- DAY BY DAY
    if kind != "daily":
        days = {}
        for sale in sales:
            d = record_date(sale.get("date"))
            if d:
                row = days.setdefault(d, [0.0, 0.0, 0.0, 0.0])
                snap = sale_snapshot(sale)
                row[0] += snap["total"]; row[1] += snap["gross_profit"]
        for expense in expenses:
            d = record_date(expense.get("date"))
            if d:
                days.setdefault(d, [0.0, 0.0, 0.0, 0.0])[2] += safe_float(expense.get("amount", 0))
        for purchase in purchases:
            d = record_date(purchase.get("date"))
            if d:
                days.setdefault(d, [0.0, 0.0, 0.0, 0.0])[3] += safe_float(purchase.get("total_cost", 0))
        wd, al = [5, 9, 9, 8, 8], ["l", "r", "r", "r", "r"]
        out += ["", "DAY BY DAY", rule]
        out += fmt_row(["DATE", "SALES", "NET", "EXPNS", "BOUGHT"], wd, al)
        out.append(rule)
        if days:
            for d in sorted(days):
                s, p, e, b = days[d]
                out += fmt_row([d.strftime("%d/%m"), num(s), num(p - e), num(e), num(b)], wd, al)
            out.append(rule)
            out += fmt_row(["TOTAL", num(gross_sales), num(net_profit), num(expenses_total), num(stock_bought)], wd, al)
        else:
            out.append("No activity in this period.")
        out.append(rule)

    # ---------------------------------------------------------- ITEMS SOLD
    wd, al = [11, 12, 5, 7, 9], ["l", "l", "r", "r", "r"]
    out += ["", "ITEMS SOLD", rule]
    if sales:
        out += fmt_row(["DATE", "ITEM", "QTY", "PRICE", "TOTAL"], wd, al)
        out.append(rule)
        for sale in sales:
            snap = sale_snapshot(sale)
            out += fmt_row([short_stamp(sale.get("date")), cap(sale.get("product", "")),
                            f"{snap['qty']:g}", num(snap["selling_price"]), num(snap["total"])], wd, al, wrap=1)
        out.append(rule)
        out.append(_lr("TOTAL SALES:", num(gross_sales), W))
    else:
        out.append("No sales in this period.")
    out.append(rule)

    # ---------------------------------------------------------- STOCK PURCHASED
    wd, al = [11, 12, 5, 7, 9], ["l", "l", "r", "r", "r"]
    out += ["", "STOCK PURCHASED", rule]
    if purchases:
        out += fmt_row(["DATE", "ITEM", "QTY", "COST", "TOTAL"], wd, al)
        out.append(rule)
        for purchase in purchases:
            out += fmt_row([short_stamp(purchase.get("date")), cap(purchase.get("product", "")),
                            f"{safe_float(purchase.get('qty', 0)):g}",
                            num(purchase.get("unit_cost", 0)), num(purchase.get("total_cost", 0))], wd, al, wrap=1)
        out.append(rule)
        out.append(_lr("TOTAL STOCK BOUGHT:", num(stock_bought), W))
    else:
        out.append("No stock purchased in this period.")
    out.append(rule)

    # ---------------------------------------------------------- EXPENSES
    wd, al = [11, 25, 10], ["l", "l", "r"]
    out += ["", "EXPENSES", rule]
    if expenses:
        out += fmt_row(["DATE", "REASON", "TOTAL"], wd, al)
        out.append(rule)
        for expense in expenses:
            out += fmt_row([short_stamp(expense.get("date")), cap(expense.get("description", "Expense")),
                            num(expense.get("amount", 0))], wd, al, wrap=1)
        out.append(rule)
        out.append(_lr("TOTAL EXPENSES:", num(expenses_total), W))
    else:
        out.append("No expenses in this period.")
    out.append(rule)
    return _wrap_report("\n".join(out), W)


def receipt_text(shop, sales, receipt_no, cash=None, change=None, reprint=False):
    """Table receipt. Used for the receipt at sale time AND for reprints from saved sales."""
    W = RECEIPT_WIDTH
    first = sales[0] if sales else {}
    when = parse_record_datetime(first.get("date"))
    date_text = when.strftime("%d/%m/%Y %H:%M") if when else str(first.get("date", ""))
    customer = str(first.get("customer_name") or "").strip()
    total = sum(sale_snapshot(x)["total"] for x in sales)

    out = ["=" * W]
    for part in textwrap.wrap(shop.upper(), W) or [""]:
        out.append(part.center(W).rstrip())
    out.append(("SALES RECEIPT" + ("  (REPRINT)" if reprint else "")).center(W).rstrip())
    out += ["=" * W, f"Receipt: {receipt_no}", f"Date:    {date_text}"]
    if customer:
        out += textwrap.wrap("Customer: " + customer, W)
    wd, al = [16, 4, 8, 9], ["l", "r", "r", "r"]
    out += ["-" * W]
    out += fmt_row(["ITEM", "QTY", "PRICE", "TOTAL"], wd, al)
    out.append("-" * W)
    for sale in sales:
        snap = sale_snapshot(sale)
        out += fmt_row([cap(sale.get("product", "")), f"{snap['qty']:g}", num(snap["selling_price"]), num(snap["total"])], wd, al, wrap=0)
    out += ["-" * W, _lr("TOTAL", num(total), W)]
    if cash is None:
        cash = first.get("cash_paid")
        change = first.get("change_given")
    if cash is not None:
        if change is None:
            change = safe_float(cash) - total
        out += [_lr("CASH", num(cash), W), _lr("CHANGE", num(max(0.0, safe_float(change))), W)]
        owed = sum(safe_float(x.get("credit_amount")) for x in sales)
        if owed > 0.004:
            out += [_lr("BALANCE OWED (CREDIT)", num(owed), W)]
    out += ["=" * W, "THANK YOU".center(W).rstrip(), "=" * W]
    return _wrap_report("\n".join(out), W)


def mono_font():
    """A fixed-width font so table columns line up on screen."""
    candidates = []
    try:
        import kivy
        candidates.append(os.path.join(kivy.kivy_data_dir, "fonts", "RobotoMono-Regular.ttf"))
    except Exception:
        pass
    candidates += ["/system/fonts/DroidSansMono.ttf", "/system/fonts/CutiveMono.ttf"]
    for path in candidates:
        try:
            if os.path.exists(path):
                return path
        except Exception:
            pass
    return None


def mono_kwargs():
    font = mono_font()
    return {"font_name": font} if font else {}


def group_orders(sales):
    """Group sale lines into orders (one order per receipt).

    `sales` must already be in the order the sales were made (get_period_records
    sorts them). Older records without a receipt number are grouped by their
    timestamp, so every line still lands in an order.
    """
    orders = {}
    for sale in sales:
        receipt = str(sale.get("receipt_no") or "").strip()
        key = receipt or "legacy-" + str(sale.get("date", ""))
        order = orders.get(key)
        if order is None:
            order = orders[key] = {
                "receipt_no": receipt,
                "when": parse_record_datetime(sale.get("date")),
                "customer": str(sale.get("customer_name") or "").strip(),
                "items": [],
                "lines": [],
                "total": 0.0,
            }
        snap = sale_snapshot(sale)
        order["items"].append({
            "name": str(sale.get("product", "")),
            "unit": str(sale.get("unit") or ""),
            "qty": snap["qty"],
            "price": snap["selling_price"],
            "total": snap["total"],
        })
        order["lines"].append(sale)
        order["total"] += snap["total"]
    return list(orders.values())


class DB:

    def __init__(self):

        self.categories = load_json(
            "categories.json",
            DEFAULT_CATEGORIES.copy()
        )

        self.products = load_json(
            "products.json",
            []
        )

        self.sales = load_json(
            "sales.json",
            []
        )

        self.expenses = load_json(
            "expenses.json",
            []
        )

        self.settings = load_json(
            "settings.json",
            {
                "business_name": "My Shop"
            }
        )

        # Weeks and months are settled and saved automatically when they end.
        # Days are NOT stored: a day is always rebuilt from the sales and is
        # included in its week's statement.
        self.weekly_settlements = load_json(
            "weekly_settlements.json",
            {}
        )

        self.monthly_settlements = load_json(
            "monthly_settlements.json",
            {}
        )

        # Every stock purchase (new product or restock) is logged here with
        # its date, so "stock purchased on a date" can be listed in statements.
        self.purchases = load_json(
            "purchases.json",
            []
        )

        # Legacy owner-capital data is retained for backward compatibility.
        # New Financial Setup derives opening equity from opening assets minus liabilities.
        self.capital = load_json(
            "capital.json",
            {
                "opening_amount": 0.0,
                "opening_date": None,
                "transactions": []
            }
        )

        # Empty folders created by the user in the product shelves (path lists).
        self.shelf_folders = load_json("shelf_folders.json", [])

        # Append-only financial ledger (investments, loans, supplier/customer payments, returns,
        # write-offs, opening balances...). Existing records are never rewritten by it.
        self.ledger = load_json("ledger.json", [])
        fin_apply_settings(self)
        if fin_ensure(self):
            try:
                save_json("products.json", self.products)
                save_json("ledger.json", self.ledger)
            except Exception:
                pass

    def log_purchase(self, product_name, qty, unit, unit_cost, total_cost, category,
                     supplier="", paid_amount=None, method="cash", product_pid=""):
        paid = total_cost if paid_amount is None else paid_amount
        self.purchases.append({
            "date": datetime.now().isoformat(),
            "pid": "B-" + uuid.uuid4().hex[:16],
            "product": product_name,
            "product_pid": product_pid,
            "qty": qty,
            "unit": unit,
            "unit_cost": unit_cost,
            "total_cost": total_cost,
            "category": category,
            "supplier": supplier,
            "paid_amount": paid,
            "method": method,
            "status": "paid" if total_cost - paid < 0.005 else ("unpaid" if paid < 0.005 else "part-paid"),
        })

    def save(self):

        save_json(
            "categories.json",
            self.categories
        )

        save_json(
            "products.json",
            self.products
        )

        save_json(
            "sales.json",
            self.sales
        )

        save_json(
            "expenses.json",
            self.expenses
        )

        save_json(
            "settings.json",
            self.settings
        )

        save_json(
            "weekly_settlements.json",
            self.weekly_settlements
        )

        save_json(
            "monthly_settlements.json",
            self.monthly_settlements
        )

        save_json(
            "purchases.json",
            self.purchases
        )

        save_json(
            "capital.json",
            self.capital
        )

        save_json(
            "shelf_folders.json",
            self.shelf_folders
        )

        save_json("ledger.json", self.ledger)

        # Multi-device sync is best-effort and never blocks local saving.
        try:
            app = App.get_running_app()
            if app is not None and hasattr(app, "schedule_sync"):
                app.schedule_sync()
        except Exception:
            pass

    def save_local_only(self):
        save_json("categories.json", self.categories)
        save_json("products.json", self.products)
        save_json("sales.json", self.sales)
        save_json("expenses.json", self.expenses)
        save_json("settings.json", self.settings)
        save_json("weekly_settlements.json", self.weekly_settlements)
        save_json("monthly_settlements.json", self.monthly_settlements)
        save_json("purchases.json", self.purchases)
        save_json("capital.json", self.capital)
        save_json("shelf_folders.json", self.shelf_folders)
        save_json("ledger.json", self.ledger)

    def _settlement_record(self, start, end, sales, expenses, books=None):
        # Position figures are as of the period end and come from the accounting engine.
        rec = period_snapshot(self, start, end, books)
        rec["orders"] = len(group_orders(sales))
        rec["units"] = sum(safe_float(s.get("qty", 0)) for s in sales)
        return rec

    def settle_periods(self):
        """Automatic settlement.

        Every week (Mon-Sun) and every month that has ENDED is settled and
        saved once. The running week/month is never settled. Sales and
        expenses are never deleted; settlement only saves the totals.
        """
        changed = False
        books = None

        for start in completed_weeks(self):
            key = start.isoformat()
            if key in self.weekly_settlements:
                continue
            s, e = period_bounds("weekly", key)
            sales, expenses = get_period_records(self, s, e)
            books = books or Books(self)
            self.weekly_settlements[key] = self._settlement_record(s, e, sales, expenses, books)
            changed = True

        for start in completed_months(self):
            key = start.strftime("%Y-%m")
            if key in self.monthly_settlements:
                continue
            s, e = period_bounds("monthly", key)
            sales, expenses = get_period_records(self, s, e)
            books = books or Books(self)
            self.monthly_settlements[key] = self._settlement_record(s, e, sales, expenses, books)
            changed = True

        if changed:
            self.save()
        return changed


# ================= RECEIPT OUTPUT: SAVE / PRINT / SHARE =================
_PRINT_KEEP = {}   # keeps the Android WebView alive while the print dialog is open


def safe_filename(name, ext=".txt"):
    base = re.sub(r"[^A-Za-z0-9._-]+", "_", str(name or "")).strip("_.") or "receipt"
    if ext and not base.lower().endswith(ext):
        base += ext
    return base


def _android_activity():
    from jnius import autoclass
    return autoclass("org.kivy.android.PythonActivity").mActivity


def _jtext(text):
    """Python str -> java.lang.CharSequence (avoids pyjnius overload errors in putExtra)."""
    from jnius import autoclass, cast
    return cast("java.lang.CharSequence", autoclass("java.lang.String")(str(text)))


def _java_write(stream, data):
    try:
        stream.write(bytearray(data))
    except Exception:
        stream.write([b - 256 if b > 127 else b for b in data])


def open_link(url):
    """tel: opens the dialer with the number, mailto: opens Gmail (any mail app if Gmail is missing),
    https: opens the browser / WhatsApp. Web browser on non-Android."""
    try:
        from jnius import autoclass
    except ImportError:
        import webbrowser
        if not webbrowser.open(url):
            raise RuntimeError("No app available to open " + url)
        return
    Intent = autoclass("android.content.Intent")
    Uri = autoclass("android.net.Uri")
    activity = _android_activity()
    uri = Uri.parse(url)
    if str(url).startswith("tel:"):
        activity.startActivity(Intent(Intent.ACTION_DIAL, uri))
        return
    if str(url).startswith("mailto:"):
        try:
            gmail = Intent(Intent.ACTION_SENDTO, uri)
            gmail.setPackage("com.google.android.gm")
            activity.startActivity(gmail)
            return
        except Exception:
            pass                      # Gmail not installed: fall through to the default mail app
        activity.startActivity(Intent(Intent.ACTION_SENDTO, uri))
        return
    activity.startActivity(Intent(Intent.ACTION_VIEW, uri))


def support_rows(data):
    """[(caption, value, url-or-None)] for the support popup. Phone / WhatsApp / Email / Website are tappable."""
    data = data if isinstance(data, dict) else {}
    links = dict(support_actions(data))
    rows = []
    for caption, key, link, hint in (("Support", "name", None, ""), ("Phone", "phone", "Call", "tap to call"),
                                     ("WhatsApp", "whatsapp", "WhatsApp", "tap to chat"),
                                     ("Email", "email", "Email", "tap to write an email"),
                                     ("Website", "website", "Website", "tap to open"),
                                     ("Hours", "hours", None, ""), ("Message", "message", None, "")):
        value = str(data.get(key) or "").strip()
        if value:
            rows.append((caption + ((" \u2022 " + hint) if (link and links.get(link)) else ""), value, links.get(link) if link else None))
    return rows, str(data.get("updated_at") or "")


def make_text_pdf(text):
    """Small dependency-free PDF (Courier). Receipts get an 80 mm roll-width page; wide
    statements get A4-width pages. Opens in any PDF viewer and prints on any printer."""
    lines = str(text).replace("\t", "    ").splitlines() or [""]
    longest = max(len(l) for l in lines)
    margin = 14.0
    if longest <= 42:
        width_pt = 226.8
        size = max(6.0, min(10.0, (width_pt - 2 * margin) / (0.6 * max(longest, 1))))
        lh = size * 1.25
        page_h = min(14000.0, len(lines) * lh + 2 * margin + 6)
    else:
        width_pt = 595.0
        size = max(5.5, min(10.0, (width_pt - 2 * margin) / (0.6 * longest)))
        lh = size * 1.25
        page_h = 842.0
    per_page = max(1, int((page_h - 2 * margin) // lh))
    pages = [lines[i:i + per_page] for i in range(0, len(lines), per_page)] or [[""]]
    objs = [b"", b"", b"<< /Type /Font /Subtype /Type1 /BaseFont /Courier /Encoding /WinAnsiEncoding >>"]
    kids = []
    for page_lines in pages:
        ops = ["BT", "/F1 %.2f Tf" % size, "%.2f TL" % lh, "%.2f %.2f Td" % (margin, page_h - margin - size)]
        for line in page_lines:
            esc = line.encode("cp1252", "replace").decode("latin-1")
            esc = esc.replace("\\", "\\\\").replace("(", "\\(").replace(")", "\\)")
            ops.append("(" + esc + ") Tj T*")
        ops.append("ET")
        stream = "\n".join(ops).encode("latin-1")
        page_no = len(objs) + 1
        objs.append(("<< /Type /Page /Parent 2 0 R /MediaBox [0 0 %.2f %.2f] /Contents %d 0 R "
                     "/Resources << /Font << /F1 3 0 R >> >> >>" % (width_pt, page_h, page_no + 1)).encode())
        objs.append(b"<< /Length %d >>\nstream\n" % len(stream) + stream + b"\nendstream")
        kids.append("%d 0 R" % page_no)
    objs[0] = b"<< /Type /Catalog /Pages 2 0 R >>"
    objs[1] = ("<< /Type /Pages /Kids [%s] /Count %d >>" % (" ".join(kids), len(pages))).encode()
    out = bytearray(b"%PDF-1.4\n")
    offsets = []
    for number, body in enumerate(objs, 1):
        offsets.append(len(out))
        out += b"%d 0 obj\n" % number + body + b"\nendobj\n"
    xref = len(out)
    out += b"xref\n0 %d\n0000000000 65535 f \n" % (len(objs) + 1)
    for off in offsets:
        out += b"%010d 00000 n \n" % off
    out += b"trailer\n<< /Size %d /Root 1 0 R >>\nstartxref\n%d\n%%%%EOF\n" % (len(objs) + 1, xref)
    return bytes(out)


def save_file_to_phone(data, filename, mime="text/plain"):
    """Save bytes where the user can find them (Android 10+: Downloads/ShopReceipts, no
    permission needed; otherwise the app's receipts folder). Returns a readable location."""
    data = bytes(data)
    activity = None
    try:
        from jnius import autoclass
        activity = _android_activity()
    except Exception:
        autoclass = None
    if activity is not None:
        try:
            if autoclass("android.os.Build$VERSION").SDK_INT >= 29:
                ContentValues = autoclass("android.content.ContentValues")
                MC = autoclass("android.provider.MediaStore$MediaColumns")
                Downloads = autoclass("android.provider.MediaStore$Downloads")
                resolver = activity.getContentResolver()
                values = ContentValues()
                values.put(MC.DISPLAY_NAME, filename)
                values.put(MC.MIME_TYPE, mime)
                values.put(MC.RELATIVE_PATH, "Download/ShopReceipts")
                uri = resolver.insert(Downloads.EXTERNAL_CONTENT_URI, values)
                if uri is None:
                    raise RuntimeError("Android refused to create the file.")
                stream = resolver.openOutputStream(uri)
                _java_write(stream, data)
                stream.flush()
                stream.close()
                return "Downloads / ShopReceipts / " + filename
        except Exception:
            pass
        try:
            ext_dir = activity.getExternalFilesDir(None)
            if ext_dir is not None:
                folder = os.path.join(str(ext_dir.getAbsolutePath()), "receipts")
                os.makedirs(folder, exist_ok=True)
                path = os.path.join(folder, filename)
                with open(path, "wb") as f:
                    f.write(data)
                return path
        except Exception:
            pass
    folder = os.path.join(os.path.dirname(data_path("settings.json")), "receipts")
    os.makedirs(folder, exist_ok=True)
    path = os.path.join(folder, filename)
    with open(path, "wb") as f:
        f.write(data)
    return path


def save_pdf_to_phone(text, filename):
    return save_file_to_phone(make_text_pdf(text), safe_filename(re.sub(r"\.txt$", "", str(filename)), ext=".pdf"),
                              "application/pdf")


def save_text_to_phone(text, filename):
    """Save a text file where the user can find it. Returns a readable location.

    Android 10+: public Downloads/ShopReceipts (no storage permission needed).
    Older Android / other platforms: the app's own receipts folder.
    """
    filename = safe_filename(filename)
    data = str(text).encode("utf-8")
    activity = None
    try:
        from jnius import autoclass
        activity = _android_activity()
    except Exception:
        autoclass = None
    if activity is not None:
        try:
            if autoclass("android.os.Build$VERSION").SDK_INT >= 29:
                ContentValues = autoclass("android.content.ContentValues")
                MC = autoclass("android.provider.MediaStore$MediaColumns")
                Downloads = autoclass("android.provider.MediaStore$Downloads")
                resolver = activity.getContentResolver()
                values = ContentValues()
                values.put(MC.DISPLAY_NAME, filename)
                values.put(MC.MIME_TYPE, "text/plain")
                values.put(MC.RELATIVE_PATH, "Download/ShopReceipts")
                uri = resolver.insert(Downloads.EXTERNAL_CONTENT_URI, values)
                if uri is None:
                    raise RuntimeError("Android refused to create the file.")
                stream = resolver.openOutputStream(uri)
                _java_write(stream, data)
                stream.flush()
                stream.close()
                return "Downloads / ShopReceipts / " + filename
        except Exception:
            pass
        try:
            ext_dir = activity.getExternalFilesDir(None)
            if ext_dir is not None:
                folder = os.path.join(str(ext_dir.getAbsolutePath()), "receipts")
                os.makedirs(folder, exist_ok=True)
                path = os.path.join(folder, filename)
                with open(path, "wb") as f:
                    f.write(data)
                return path
        except Exception:
            pass
    folder = os.path.join(os.path.dirname(data_path("settings.json")), "receipts")
    os.makedirs(folder, exist_ok=True)
    path = os.path.join(folder, filename)
    with open(path, "wb") as f:
        f.write(data)
    return path


def share_plain_text(text, title="Share Receipt"):
    """Android share sheet (WhatsApp, e-mail, SMS, printer apps...). Raises on failure."""
    from jnius import autoclass
    Intent = autoclass("android.content.Intent")
    activity = _android_activity()
    intent = Intent(Intent.ACTION_SEND)
    intent.setType("text/plain")
    intent.putExtra(Intent.EXTRA_TEXT, _jtext(text))
    activity.startActivity(Intent.createChooser(intent, _jtext(title)))


def print_text_android(title, text, on_error=None):
    """Open Android's print dialog for the text. It lists every installed printer / print
    service (Wi-Fi, Bluetooth, USB via vendor plug-ins) and 'Save as PDF'.
    Raises ImportError when not running on Android."""
    import html as _html
    from jnius import autoclass, cast
    from android.runnable import run_on_ui_thread
    activity = _android_activity()
    job = safe_filename(title, ext="")
    page = ("<html><head><meta charset='utf-8'><style>@page{margin:8mm}"
            "body{margin:0}pre{font-family:monospace;font-size:11pt;white-space:pre-wrap;margin:0}"
            "</style></head><body><pre>" + _html.escape(str(text)) + "</pre></body></html>")
    state = {"tries": 0, "progress": 0, "done": False}

    def report(e):
        if not state["done"]:
            state["done"] = True
            if on_error:
                Clock.schedule_once(lambda dt: on_error(e), 0)

    @run_on_ui_thread
    def load():
        try:
            WebView = autoclass("android.webkit.WebView")
            wv = WebView(activity)
            wv.loadDataWithBaseURL(None, page, "text/html", "UTF-8", None)
            _PRINT_KEEP["wv"] = wv
        except Exception as e:
            report(e)

    @run_on_ui_thread
    def probe():
        try:
            state["progress"] = int(_PRINT_KEEP["wv"].getProgress())
        except Exception:
            state["progress"] = -1

    @run_on_ui_thread
    def do_print():
        try:
            Context = autoclass("android.content.Context")
            wv = _PRINT_KEEP.get("wv")
            adapter = wv.createPrintDocumentAdapter(job)
            pm = cast("android.print.PrintManager", activity.getSystemService(Context.PRINT_SERVICE))
            pm.print(job, adapter, None)
            state["done"] = True
        except Exception as e:
            report(e)

    def tick(dt):
        # Runs on the Kivy thread: wait until the WebView has finished loading (up to ~4 s).
        if state["done"]:
            return False
        state["tries"] += 1
        if state["progress"] >= 100 or state["tries"] >= 14:
            do_print()
            return False
        probe()
        return True

    load()
    Clock.schedule_interval(tick, 0.3)


class Base(Screen):

    def on_pre_leave(self, *_):
        clear_selection_artifacts(self)

    def top(self, title):

        bar = BoxLayout(
            size_hint_y=None,
            height=dp(60),
            spacing=dp(10),
            padding=(dp(8), dp(8))
        )
        with bar.canvas.before:
            Color(0.08, 0.14, 0.23, 0.12)
            bar._sh = RoundedRectangle(pos=bar.pos, size=bar.size, radius=[dp(14)])
            Color(*PRIMARY)
            bar._bg = RoundedRectangle(pos=bar.pos, size=bar.size, radius=[dp(14)])
            Color(*ACCENT)
            bar._line = RoundedRectangle(pos=bar.pos, size=(dp(36), dp(3)), radius=[dp(1.5)])

        def _bar_redraw(i, *_):
            i._sh.pos = (i.x, i.y - dp(2))
            i._sh.size = i.size
            i._bg.pos = i.pos
            i._bg.size = i.size
            i._line.pos = (i.x + dp(16), i.y)
        bar.bind(pos=_bar_redraw, size=_bar_redraw)

        back = AppButton(
            text="‹ Back",
            size_hint_x=None,
            width=dp(88),
            background_color=(1, 1, 1, 0.14),
            flat=True
        )

        back.bind(on_release=self.go_back)

        bar.add_widget(back)

        heading = AppLabel(
            text=title,
            font_size=sp(18),
            bold=True,
            color=(1, 1, 1, 1),
            halign="left",
            valign="middle",
            shorten=True,
            shorten_from="right"
        )
        heading.bind(size=lambda i, v: setattr(i, "text_size", (v[0], v[1])))
        bar.add_widget(heading)

        bar.is_top_bar = True

        return bar

    def set_content(self, layout):
        """Make the screen scrollable.

        The title bar (Back button) stays pinned at the top and everything
        underneath it scrolls, so nothing is cut off on small phones, in
        landscape, or when the keyboard is open.
        """
        kids = list(reversed(layout.children))  # in the order they were added
        bar = kids[0] if kids and getattr(kids[0], "is_top_bar", False) else None
        rest = kids[1:] if bar else kids

        for kid in kids:
            layout.remove_widget(kid)

        body = BoxLayout(
            orientation="vertical",
            size_hint_y=None,
            spacing=layout.spacing
        )
        body.bind(minimum_height=body.setter("height"))
        # Centred, width-limited column so phones fill the screen and tablets
        # get a comfortable reading width instead of stretched controls.
        holder = BoxLayout(orientation="horizontal", size_hint_y=None)
        holder.add_widget(body)
        body.bind(height=holder.setter("height"))

        def _fit_width(inst, w):
            pad = max(0, (w - MAX_CONTENT_W) / 2.0)
            inst.padding = [pad, 0, pad, 0]
        holder.bind(width=_fit_width)

        for kid in rest:
            if isinstance(kid, ScrollView) and kid.children:
                # Old inner list scroller: unwrap it so there is only one
                # scroll area (nested scrolling fights the finger).
                inner = kid.children[0]
                kid.remove_widget(inner)
                body.add_widget(inner)
                continue
            if kid.size_hint_y is not None:
                # A stretchy widget would collapse to nothing inside a scroller.
                kid.size_hint_y = None
                kid.height = dp(120)
            body.add_widget(kid)

        scroll = SmoothScroll(do_scroll_x=False, bar_width=dp(4),
                            bar_color=(0.08, 0.14, 0.23, 0.35),
                            bar_inactive_color=(0.08, 0.14, 0.23, 0.12))
        scroll.add_widget(holder)

        if bar:
            layout.add_widget(bar)
        layout.add_widget(scroll)
        self.add_widget(layout)

    def scroll_wrap(self, content):
        """Wrap popup content (all fixed-height children) in a scroller."""
        content.size_hint_y = None
        content.bind(minimum_height=content.setter("height"))
        scroll = SmoothScroll(do_scroll_x=False)
        scroll.add_widget(content)
        return scroll

    def autosize_text(self, view, min_height=dp(120)):
        """Let a read-only TextInput grow with its text so the page scrolls
        instead of the box scrolling inside the page."""
        view.size_hint_y = None
        view.height = min_height

        def fit(instance, value):
            instance.height = max(min_height, value + dp(6))

        view.bind(minimum_height=fit)
        fit(view, getattr(view, "minimum_height", 0))

    def copy_text(self, text):
        try:
            from kivy.core.clipboard import Clipboard
            Clipboard.copy(text)
            self.msg("Copied.")
        except Exception as e:
            self.msg(str(e))

    def run_bg(self, work, done, fail=None):
        """Run work() on a background thread (network etc.) so the screen stays responsive.
        done(result) / fail(exception) are called back on the UI thread."""
        def runner():
            try:
                result = work()
            except Exception as exc:
                err = exc
                Clock.schedule_once(lambda dt: fail(err) if fail else None, 0)
                return
            Clock.schedule_once(lambda dt: done(result), 0)
        threading.Thread(target=runner, daemon=True).start()

    def support_card(self, height=92):
        """Prominent Support card (same everywhere): opens the support popup."""
        card = role_card("SP", "support", "Customer Support", "Call \u2022 WhatsApp \u2022 Email \u2022 Website", INFO, height=height)
        card.bind(on_release=lambda *_: Clock.schedule_once(lambda dt: self.show_support(), 0))
        return card

    def show_support(self, *_):
        """Show the support details the developer published and download the latest copy."""
        label = BoxLayout(orientation="vertical", size_hint_y=None, spacing=dp(8))
        label.bind(minimum_height=label.setter("height"))
        status = wrap_label("", font_size=sp(11), color=TEXT_MUTED)

        def open_it(url, *_):
            try:
                open_link(url)
            except Exception as exc:
                status.text = "Could not open: " + str(exc)[:90]

        def paint(note=""):
            data = cached_support()
            rows, updated = support_rows(data)
            label.clear_widgets()
            if not rows:
                label.add_widget(wrap_label("No support details have been published yet.", font_size=sp(14)))
            from kivy.utils import escape_markup
            for caption, value, url in rows:
                line = BoxLayout(orientation="vertical", size_hint_y=None, spacing=dp(1), padding=(dp(4), dp(6)))
                line.bind(minimum_height=line.setter("height"))
                line.add_widget(wrap_label(caption.upper(), font_size=sp(10), bold=True, color=TEXT_MUTED))
                if url:
                    # the phone number / e-mail / website itself is the link: tap it
                    lab = wrap_label("[ref=go][color=2F6DA3][u]" + escape_markup(value) + "[/u][/color][/ref]",
                                     font_size=sp(17), bold=True, min_h=dp(38), markup=True)
                    lab.bind(on_ref_press=lambda _w, _r, u=url: open_it(u))
                else:
                    lab = wrap_label(value, font_size=sp(14), min_h=dp(26))
                line.add_widget(lab)
                label.add_widget(line)
            status.text = note or (("Last updated: " + updated[:16].replace("T", " ")) if updated else "")

        def download(*_):
            if not online_configured():
                paint("Online service is not configured.")
                return
            status.text = "Downloading the latest support details..."

            def work():
                try:
                    fetch_support_online()
                    note = ""
                except Exception as exc:
                    note = "Could not refresh (" + str(exc)[:80] + "). Showing saved details."
                Clock.schedule_once(lambda dt: paint(note), 0)
            threading.Thread(target=work, daemon=True).start()

        def copy(*_):
            try:
                from kivy.core.clipboard import Clipboard
                Clipboard.copy("\n".join(c.split(" \u2022")[0] + ": " + v for c, v, _u in support_rows(cached_support())[0]))
                status.text = "Support details copied."
            except Exception as exc:
                status.text = str(exc)

        box = BoxLayout(orientation="vertical", padding=dp(10), spacing=dp(8))
        sv = SmoothScroll(do_scroll_x=False, bar_width=dp(4))
        sv.add_widget(label)
        box.add_widget(sv)
        box.add_widget(status)
        row = GridLayout(cols=2, spacing=dp(8), size_hint_y=None, height=dp(46))
        refresh_btn = AppButton(text="Refresh")
        copy_btn = AppButton(text="Copy")
        refresh_btn.bind(on_release=download)
        copy_btn.bind(on_release=copy)
        row.add_widget(refresh_btn)
        row.add_widget(copy_btn)
        box.add_widget(row)
        paint()
        Popup(title=APP_NAME + " - Support", content=box, size_hint=(.94, .8)).open()
        download()

    def _out_name(self, title="Receipt", filename=None):
        if filename:
            return safe_filename(filename)
        return safe_filename(f"{title}_{datetime.now().strftime('%Y%m%d_%H%M%S')}")

    def save_text(self, text, title="Receipt", filename=None):
        """Save the receipt/statement to the phone as a PDF (plain text if PDF fails)."""
        name = self._out_name(title, filename)
        try:
            self.msg("Saved to phone (PDF):\n" + save_pdf_to_phone(text, name))
        except Exception as pdf_error:
            try:
                self.msg("Saved to phone (text):\n" + save_text_to_phone(text, name))
            except Exception as e:
                self.msg("Could not save the file:\n" + str(e) + "\n(" + str(pdf_error)[:80] + ")")

    def print_text(self, text, title="Receipt", filename=None):
        """Open the Android print dialog (any printer, or Save as PDF). If it cannot open,
        a PDF copy is saved automatically so the receipt is never lost."""
        def failed(e):
            note = ""
            try:
                note = "\n\nA PDF copy was saved to:\n" + save_pdf_to_phone(text, self._out_name(title, filename)) + \
                       "\nOpen it from your Files app to print or share it."
            except Exception:
                note = "\n\nUse Save PDF or Share instead."
            self.msg("The print dialog could not open:\n" + str(e)[:160] + note)
        try:
            print_text_android(title, text, on_error=failed)
        except ImportError:
            # Not running on Android (e.g. testing on a computer): keep a PDF instead.
            try:
                where = save_pdf_to_phone(text, self._out_name(title, filename))
                self.msg("Printing is only available on Android.\nA PDF copy was saved to:\n" + where)
            except Exception as e:
                self.msg("Printing is only available on Android.\n" + str(e))
        except Exception as e:
            failed(e)

    def share_text(self, text, note=""):
        """Opens the Android share sheet: WhatsApp, SMS, e-mail, printer apps..."""
        try:
            share_plain_text(text)
        except Exception as e:
            extra = ""
            try:
                extra = "\n\nA copy was saved to:\n" + save_text_to_phone(text, self._out_name("Receipt"))
            except Exception:
                pass
            self.msg((note + "\n\n" if note else "") + "Could not open Android share: " + str(e) + extra)

    def show_text_popup(self, text, title, filename=None):
        text = str(text)
        longest = max([len(l) for l in text.splitlines()] or [0])
        size = 13 if longest <= 34 else 12 if longest <= 40 else 11 if longest <= 48 else 10
        layout = BoxLayout(orientation="vertical", padding=dp(8), spacing=dp(6))
        view = AppLabel(text=text, font_size=sp(size), halign="left", valign="top", size_hint_y=None, **mono_kwargs())
        view.bind(width=lambda inst, w: setattr(inst, "text_size", (max(w-dp(12), dp(80)), None)))
        view.bind(texture_size=lambda inst, ts: setattr(inst, "height", ts[1] + dp(12)))
        receipt_scroll = SmoothScroll(do_scroll_x=False, bar_width=dp(4))
        receipt_scroll.add_widget(view)
        layout.add_widget(receipt_scroll)
        buttons = GridLayout(cols=2, spacing=dp(6), size_hint_y=None, height=dp(100))
        copy = AppButton(text="Copy")
        save = AppButton(text="Save PDF")
        share = AppButton(text="Share")
        prt = AppButton(text="Print")
        for b in (copy, save, share, prt):
            buttons.add_widget(b)
        layout.add_widget(buttons)
        pop = Popup(title=self.shop_name() + " - " + title, content=layout, size_hint=(.95, .85))
        copy.bind(on_release=lambda *_: self.copy_text(text))
        save.bind(on_release=lambda *_: self.save_text(text, title, filename))
        share.bind(on_release=lambda *_: self.share_text(text))
        prt.bind(on_release=lambda *_: self.print_text(text, title, filename))
        pop.open()

    def go_back(self, *_):
        """Keep navigation inside the role the user authenticated into."""
        app = self.manager.app
        if self.name == "admin":
            app.admin_session = False
            self.manager.current = "home"
        elif self.name == "cashier":
            app.cashier_session = False
            self.manager.current = "home"
        elif getattr(app, "admin_session", False):
            self.manager.current = "admin"
        elif getattr(app, "cashier_session", False):
            self.manager.current = "cashier"
        else:
            self.manager.current = "home"

    def msg(self, text):

        lbl = AppLabel(text=str(text), size_hint_y=None, halign="center", valign="middle")
        lbl.bind(width=lambda o, w: setattr(o, "text_size", (w, None)))
        lbl.bind(texture_size=lambda o, ts: setattr(o, "height", max(ts[1] + dp(12), dp(80))))
        sv = SmoothScroll(do_scroll_x=False, bar_width=dp(4))
        sv.add_widget(lbl)
        Popup(title=APP_NAME, content=sv, size_hint=(.9, .4)).open()

    def shop_name(self):

        return self.manager.app.confirmed_shop_name()


class Home(Base):
    """Role selection screen. Operational users go to Cashier; management goes through Admin authentication."""
    def on_pre_enter(self, *_):
        _apply_palette(_HOME_PALETTE)          # red / black / yellow, Home only
        try:
            self._build_home()
        finally:
            _apply_palette(_ORIG_PALETTE)      # every other screen keeps the original colours
        try:
            self.sync_indicator.color = sync_status_color(getattr(self.manager.app, "_sync_status", ""))
        except Exception:
            pass

    def _build_home(self, *_):
        self.clear_widgets()
        app = self.manager.app
        layout = BoxLayout(orientation="vertical", padding=(dp(16), dp(14)), spacing=dp(14))
        # Branding comes from the registered business name, never a fixed shop name.
        layout.add_widget(hero_card(APP_NAME, app.confirmed_shop_name(), "Choose the area you need to use.", logo=APP_LOGO))

        left = getattr(app, "license_days_left", None)
        if left is not None and left <= 14:
            layout.add_widget(wrap_label(("License expires TODAY. Request a renewal now." if left <= 0 else
                                          "License expires in %d day%s. Request a renewal soon." % (left, "" if left == 1 else "s")),
                                         font_size=sp(12), bold=True, color=DANGER))
        sync_card = Card(orientation="vertical", size_hint_y=None, padding=dp(14), spacing=dp(8))
        sync_card.bind(minimum_height=sync_card.setter("height"))
        sync_card.add_widget(wrap_label("CLOUD SYNC", font_size=sp(11), bold=True, color=TEXT_MUTED))
        self.sync_indicator = wrap_label(app.sync_summary(), font_size=sp(12), bold=True)
        sync_card.add_widget(self.sync_indicator)
        sync_now = AppButton(text="Sync Now", font_size=sp(13), size_hint_y=None, height=dp(44))
        sync_now.bind(on_release=lambda *_: app.sync_now(force=True))
        sync_card.add_widget(sync_now)
        layout.add_widget(sync_card)

        layout.add_widget(wrap_label("SELECT YOUR ROLE", font_size=sp(12), bold=True, color=TEXT_MUTED))
        cashier = role_card("CA", "cashier", "Cashier", "Sales \u2022 Receipts \u2022 Expenses", ACCENT)
        admin = role_card("AD", "admin", "Admin", "Inventory \u2022 Prices \u2022 Statements \u2022 Settings", PRIMARY)
        cashier.bind(on_release=self.open_cashier)
        admin.bind(on_release=self.open_admin_login)
        layout.add_widget(cashier)
        if not device_is_employee():
            layout.add_widget(admin)      # employee phones only ever see the Cashier area
        self.set_content(layout)

    def open_cashier(self, *_):
        app = self.manager.app
        app.admin_session = False
        app.cashier_session = True
        self.manager.current = "cashier"

    def open_admin_setup(self):
        """First use: the owner creates the Admin password (nothing is hard-coded)."""
        app = self.manager.app
        field = lambda hint: AppTextInput(hint_text=hint, password=True, multiline=False, size_hint_y=None, height=dp(46))
        new_pw = field("Create admin password (min. %d characters)" % ADMIN_MIN_LEN)
        confirm = field("Confirm password")
        status = wrap_label("", font_size=sp(12), color=DANGER)
        intro = wrap_label("First-time setup. Create the password that protects Admin (prices, stock, "
                           "statements and settings). There is no default password, so keep this one safe.",
                           font_size=sp(12), color=TEXT_MUTED)
        buttons = GridLayout(cols=2, spacing=dp(6), size_hint_y=None, height=dp(46))
        save = AppButton(text="Save Password")
        cancel = AppButton(text="Cancel")
        buttons.add_widget(save); buttons.add_widget(cancel)
        box = BoxLayout(orientation="vertical", padding=dp(10), spacing=dp(8))
        for w in (wrap_label("SET UP ADMIN PASSWORD", font_size=sp(14), bold=True), intro, new_pw, confirm, status, buttons):
            box.add_widget(w)
        popup = Popup(title=app_name(app), content=self.scroll_wrap(box), size_hint=(.92, .72))
        cancel.bind(on_release=lambda *_: popup.dismiss())

        def do_save(*_):
            a, b = new_pw.text.strip(), confirm.text.strip()
            if len(a) < ADMIN_MIN_LEN:
                status.text = "Password must be at least %d characters." % ADMIN_MIN_LEN
            elif a == LEGACY_DEFAULT_ADMIN:
                status.text = "Please choose a different password."
            elif a != b:
                status.text = "Passwords do not match."
            else:
                app.db.settings["admin_password"] = a
                app.db.save()
                popup.dismiss()
                app.admin_session = True
                app.cashier_session = False
                self.manager.current = "admin"
        save.bind(on_release=do_save)
        popup.open()

    def open_admin_login(self, *_):
        if device_is_employee():
            self.msg("Admin is only available on the administrator's phone.")
            return
        if not admin_password_value(self.manager.app.db):
            self.open_admin_setup()
            return
        box = BoxLayout(orientation="vertical", padding=dp(10), spacing=dp(8))
        password = AppTextInput(hint_text="Admin password", password=True, multiline=False, size_hint_y=None, height=dp(46))
        status = AppLabel(text="", size_hint_y=None, height=dp(40), font_size=sp(12))
        buttons = GridLayout(cols=2, spacing=dp(6), size_hint_y=None, height=dp(46))
        login = AppButton(text="ENTER ADMIN")
        cancel = AppButton(text="CANCEL")
        buttons.add_widget(login); buttons.add_widget(cancel)
        box.add_widget(AppLabel(text="ADMIN ACCESS", bold=True, size_hint_y=None, height=dp(35)))
        box.add_widget(password); box.add_widget(status); box.add_widget(buttons)
        popup = Popup(title=app_name(self.manager.app), content=self.scroll_wrap(box), size_hint=(.88, .5))
        cancel.bind(on_release=lambda *_: popup.dismiss())
        login.bind(on_release=lambda *_: self.check_admin(password, status, popup))
        popup.open()

    def check_admin(self, field, status, popup):
        app = self.manager.app
        locked = getattr(app, "_admin_locked_until", 0)
        if time.time() < locked:
            status.text = "Too many attempts. Try again in %d seconds." % int(locked - time.time() + 1)
            return
        entered = field.text.strip()
        configured = admin_password_value(app.db)
        if entered and configured and entered == configured:
            app._admin_fails = 0
            popup.dismiss()
            app.admin_session = True
            app.cashier_session = False
            self.manager.current = "admin"
        else:
            app._admin_fails = getattr(app, "_admin_fails", 0) + 1
            if app._admin_fails >= 5:
                app._admin_fails = 0
                app._admin_locked_until = time.time() + 30
                status.text = "Too many attempts. Wait 30 seconds."
            else:
                status.text = "Incorrect admin password."

def app_name(app):
    return APP_NAME


# ---- Admin password: there is NO built-in default. The owner creates it on first use. ----
LEGACY_DEFAULT_ADMIN = "admin123"   # old built-in default: never accepted as a login any more;
                                    # only used to recognise installs that never chose a password
ADMIN_MIN_LEN = 6


def admin_password_value(db):
    """The admin password the owner chose, or '' when none has been set yet."""
    pw = str(db.settings.get("admin_password", "") or "").strip()
    return "" if (not pw or pw == LEGACY_DEFAULT_ADMIN) else pw


class AdminHome(Base):
    """Management-only dashboard. The accounting engine and license system remain elsewhere unchanged."""
    def on_pre_enter(self, *_):
        self.clear_widgets()
        layout = BoxLayout(orientation="vertical", padding=dp(12), spacing=dp(10))
        layout.add_widget(self.top("Admin Dashboard"))
        layout.add_widget(hero_card("Management Console", self.shop_name()))
        buttons = GridLayout(cols=2, spacing=dp(10), size_hint_y=None, row_default_height=dp(128), row_force_default=True)
        buttons.bind(minimum_height=buttons.setter("height"))
        buttons.bind(width=lambda g, w: setattr(g, "cols", 3 if w >= dp(560) else 2))
        items = [
            ("Products / Stock", "products", "PR"),
            ("Daily / Weekly / Monthly Statements", "reports", "ST"),
            ("Expense History", "expenses", "EX"),
            ("Stock Purchases", "purchases", "PU"),
            ("Capital & Finance", "finance", "FS"),
            ("Customer & Supplier Debts", "debts", "DB"),
            ("Activation / License", "license", "LI"),
            ("Cloud Devices / Join Code", "devices", "DV"),
        ]

        def open_target(target):
            # Let the pressed tile repaint first, then open the screen (heavy screens
            # build their content on entry; this keeps the tap feeling instant).
            Clock.schedule_once(lambda dt: setattr(self.manager, "current", target), 0)

        for idx, (text, target, code) in enumerate(items):
            b = ActionCard(orientation="vertical", padding=dp(10), spacing=dp(8))
            b.add_widget(Badge(code, accent=TILE_COLORS[idx % len(TILE_COLORS)], size_dp=56, icon_key=target,
                               pos_hint={"center_x": .5}))
            lab = AppLabel(text=text, font_size=sp(13), bold=True, halign="center", valign="top")
            lab.bind(size=lambda i, v: setattr(i, "text_size", (v[0], v[1])))
            b.add_widget(lab)
            b.bind(on_release=lambda _, t=target: open_target(t))
            buttons.add_widget(b)
        layout.add_widget(buttons)
        layout.add_widget(self.support_card(height=84))
        change = AppButton(text="Change Password", font_size=sp(13), size_hint_y=None, height=dp(52))
        change.bind(on_release=self.change_password)
        layout.add_widget(change)
        self.set_content(layout)

    def change_password(self, *_):
        """Change the admin password. The current password must be entered first."""
        app = self.manager.app

        def make_field(hint):
            return AppTextInput(hint_text=hint, password=True, multiline=False, size_hint_y=None, height=dp(46))

        current = make_field("Current password")
        new_pw = make_field("New password (min. %d characters)" % ADMIN_MIN_LEN)
        confirm = make_field("Confirm new password")
        status = AppLabel(text="", size_hint_y=None, height=dp(44), font_size=sp(12), color=DANGER)
        status.bind(width=lambda inst, w: setattr(inst, "text_size", (w, None)))
        buttons = GridLayout(cols=2, spacing=dp(6), size_hint_y=None, height=dp(46))
        save = AppButton(text="SAVE PASSWORD")
        cancel = AppButton(text="CANCEL")
        buttons.add_widget(save)
        buttons.add_widget(cancel)

        box = BoxLayout(orientation="vertical", padding=dp(10), spacing=dp(8))
        box.add_widget(AppLabel(text="CHANGE ADMIN PASSWORD", bold=True, size_hint_y=None, height=dp(32)))
        for w in (current, new_pw, confirm, status, buttons):
            box.add_widget(w)

        popup = Popup(title=self.shop_name() + " - Admin", content=self.scroll_wrap(box), size_hint=(.92, .7))
        cancel.bind(on_release=lambda *_: popup.dismiss())

        def do_save(*_):
            # Home.check_admin compares the stripped input, so strip here too.
            configured = admin_password_value(app.db)
            old = current.text.strip()
            new = new_pw.text.strip()
            again = confirm.text.strip()
            if old != configured:
                status.text = "Current password is incorrect."
            elif len(new) < ADMIN_MIN_LEN:
                status.text = "New password must be at least %d characters." % ADMIN_MIN_LEN
            elif new == LEGACY_DEFAULT_ADMIN:
                status.text = "Please choose a different password."
            elif new != again:
                status.text = "New passwords do not match."
            elif new == configured:
                status.text = "New password must be different from the current one."
            else:
                app.db.settings["admin_password"] = new
                app.db.save()
                popup.dismiss()
                self.msg("Admin password changed.\nUse the new password next time you enter Admin.")

        save.bind(on_release=do_save)
        popup.open()


class LiveToday(Base):
    """Real-time view of today's activity. It reads today's records directly and does not wait for settlement."""

    def _line(self, left, right="", bold=False, size=12, left_width=.5):
        row = BoxLayout(orientation="horizontal", size_hint_y=None, height=dp(24))
        for text, hint, align in ((left, left_width, "left"), (right, 1 - left_width, "right")):
            lab = AppLabel(text=text, bold=bold, font_size=sp(size), halign=align, valign="middle",
                        size_hint_x=hint, shorten=True, shorten_from="right")
            lab.bind(size=lambda inst, s: setattr(inst, "text_size", s))
            row.add_widget(lab)
        return row

    def order_card(self, number, order):
        """One order (receipt) with every item sold in it."""
        from kivy.graphics import Color, Rectangle
        card = BoxLayout(orientation="vertical", size_hint_y=None, padding=dp(10), spacing=dp(2))
        card.bind(minimum_height=card.setter("height"))
        with card.canvas.before:
            Color(*CARD_BG)
            rect = RoundedRectangle(pos=card.pos, size=card.size, radius=[dp(10)])
        card.bind(pos=lambda inst, v: setattr(rect, "pos", v), size=lambda inst, v: setattr(rect, "size", v))

        when = order["when"].strftime("%H:%M") if order["when"] else "--:--"
        head = f"ORDER {number}  •  {when}"
        if order["receipt_no"]:
            head += f"  •  #{order['receipt_no']}"
        card.add_widget(self._line(head, bold=True, size=13, left_width=1))
        if order["customer"]:
            card.add_widget(self._line("Customer: " + order["customer"], left_width=1))
        for item in order["items"]:
            card.add_widget(self._line(
                item["name"],
                f"{item['qty']:g} × {money(item['price'])} = {money(item['total'])}",
                left_width=.42))
        card.add_widget(self._line("Order total", money(order["total"]), bold=True))
        return card

    def on_pre_enter(self, *_):
        self._order_limit = 40
        self._build_live()

    def _build_live(self):
        self.clear_widgets()
        db = self.manager.app.db
        today = today_date()
        tomorrow = today + __import__("datetime").timedelta(days=1)
        sales, expenses = get_period_records(db, today, tomorrow)
        purchases_today = get_period_purchases(db, today, tomorrow)
        fin = fin_compute(db, today, tomorrow)
        fp, pos = fin["period"], fin["position"]
        stock_bought_today = fp["stock_purchased"]
        units = fp["units"]
        now_text = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

        layout = BoxLayout(orientation="vertical", padding=dp(8), spacing=dp(5))
        layout.add_widget(self.top("Live Today / Shop Status"))
        layout.add_widget(AppLabel(text=self.shop_name(), bold=True, font_size=sp(19), size_hint_y=None, height=dp(34)))
        layout.add_widget(AppLabel(text="LIVE DATA — updated when this screen opens. No settlement required.", font_size=sp(11), size_hint_y=None, height=dp(28)))
        layout.add_widget(AppLabel(text="As of: " + now_text, font_size=sp(11), size_hint_y=None, height=dp(24)))

        sync_lab = AppLabel(text=fin_sync_line(self.manager.app), font_size=sp(11), size_hint_y=None, height=dp(48), halign="center", valign="middle")
        sync_lab.bind(width=lambda i, w: setattr(i, "text_size", (w, None)))
        layout.add_widget(sync_lab)

        def section(title, rows):
            layout.add_widget(AppLabel(text=title, bold=True, font_size=sp(13), size_hint_y=None, height=dp(30)))
            for left, value, bold in rows:
                layout.add_widget(self._line(left, value, bold=bold, size=12, left_width=.58))
        ok = fin["setup_done"]
        shown = lambda v: fin_fmt(v) if ok else "not set up"
        section("TODAY ONLY", [
            ("Sales", fin_fmt(fp["gross_sales"]), False), ("Discounts & returns", fin_fmt(fp["discounts"] + fp["returns"]), False),
            ("Cost of goods sold", fin_fmt(fp["cogs"]), False), ("Gross profit", fin_fmt(fp["gross_profit"]), True),
            ("Expenses & other costs", fin_fmt(fp["operating_expenses"] + fp["other_costs"]), False),
            ("NET PROFIT TODAY", fin_fmt(fp["net_profit"]), True), ("Units sold", f"{units:g}", False),
            ("Stock bought today", fin_fmt(fp["stock_purchased"]), False), ("  paid now", fin_fmt(fp["stock_purchased_paid"]), False),
            ("  on credit", fin_fmt(fp["stock_purchased_credit"]), False),
            ("Owner investments", fin_fmt(fp["owner_investments"]), False), ("Owner withdrawals", fin_fmt(fp["owner_withdrawals"]), False)])
        section("CURRENT BALANCES (not daily figures)", [
            ("Inventory capital (at cost)", fin_fmt(pos["inventory"]), True), ("Cash", shown(pos["cash"]), False),
            ("Customers owe us", fin_fmt(pos["receivables"]), False), ("We owe suppliers", fin_fmt(pos["payables"]), False),
            ("Total assets", shown(pos["total_assets"]), False),
            ("Total liabilities", fin_fmt(pos["total_liabilities"]), False),
            ("NET BUSINESS CAPITAL", shown(pos["net_capital"]) if ok else fin_fmt(pos["ending_equity"]) + " (est.)", True)])
        layout.add_widget(AppLabel(text="Stock at selling prices (not capital): " + fin_fmt(sum(max(0.0, safe_float(p.get("qty"))) * max(0.0, safe_float(p.get("sell"))) for p in db.products)),
                                   font_size=sp(11), size_hint_y=None, height=dp(26)))
        full = AppButton(text="FULL CAPITAL DASHBOARD / RECONCILE", size_hint_y=None, height=dp(44), background_color=INFO)
        full.bind(on_release=lambda *_: setattr(self.manager, "current", "finance"))
        layout.add_widget(full)

        layout.add_widget(AppLabel(text=f"STOCK PURCHASE BREAKDOWN TODAY — {len(purchases_today)} PURCHASE(S)", bold=True, size_hint_y=None, height=dp(32)))
        if purchases_today:
            for purchase in purchases_today:
                layout.add_widget(self._line(
                    str(purchase.get("product", "Stock")),
                    f"{safe_float(purchase.get('qty', 0)):g} {purchase.get('unit', '')} × {money(purchase.get('unit_cost', 0))} = {money(purchase.get('total_cost', 0))}",
                    left_width=.43, size=11))
            layout.add_widget(self._line("TOTAL STOCK PURCHASED TODAY", money(stock_bought_today), bold=True, size=12))
        else:
            layout.add_widget(AppLabel(text="No stock purchases recorded today.", size_hint_y=None, height=dp(28), font_size=sp(11)))

        refresh = AppButton(text="REFRESH LIVE TOTALS", size_hint_y=None, height=dp(44))
        refresh.bind(on_release=lambda *_: self.on_pre_enter())
        layout.add_widget(refresh)

        # ---- items sold today, grouped by order, in the order they were sold
        orders = group_orders(sales)
        layout.add_widget(AppLabel(text=f"ITEMS SOLD TODAY — {len(orders)} ORDER(S)", bold=True, size_hint_y=None, height=dp(34)))
        if orders:
            limit = getattr(self, "_order_limit", 40)
            for number, order in enumerate(orders[:limit], 1):
                layout.add_widget(self.order_card(number, order))
            if len(orders) > limit:
                more = AppButton(text="Show 40 more orders (" + str(len(orders) - limit) + " not shown)",
                                 size_hint_y=None, height=dp(46), background_color=SLATE)
                def show_more(*_):
                    self._order_limit = limit + 40
                    self._build_live()
                more.bind(on_release=show_more)
                layout.add_widget(more)
        else:
            layout.add_widget(AppLabel(text="No items sold today yet.", size_hint_y=None, height=dp(32)))

        # ---- hourly breakdown
        layout.add_widget(AppLabel(text="SALES BY HOUR", bold=True, size_hint_y=None, height=dp(34)))
        hours = {}
        for sale in sales:
            when = parse_record_datetime(sale.get("date"))
            if when:
                entry = hours.setdefault(when.hour, {"sales": 0.0, "orders": set()})
                entry["sales"] += sale_snapshot(sale)["total"]
                entry["orders"].add(str(sale.get("receipt_no") or sale.get("date")))
        if hours:
            for h in sorted(hours):
                entry = hours[h]
                layout.add_widget(AppLabel(
                    text=f"{h:02d}:00–{h:02d}:59   |   Sales: {money(entry['sales'])}   |   Orders: {len(entry['orders'])}",
                    size_hint_y=None, height=dp(32), font_size=sp(12)))
        else:
            layout.add_widget(AppLabel(text="No sales recorded today yet.", size_hint_y=None, height=dp(32)))
        self.set_content(layout)


class CashierHome(Base):
    """Simple operational dashboard; no inventory editing or management controls."""
    def on_pre_enter(self, *_):
        self.clear_widgets()
        layout = BoxLayout(orientation="vertical", padding=dp(12), spacing=dp(12))
        layout.add_widget(self.top("Cashier Dashboard"))
        layout.add_widget(hero_card("Cashier", self.shop_name()))
        sale = role_card("SL", "sale", "New Sale", "Search \u2022 Cart \u2022 Receipt", ACCENT, height=108)
        sale.bind(on_release=lambda *_: Clock.schedule_once(lambda dt: setattr(self.manager, "current", "sale"), 0))
        layout.add_widget(sale)
        past = role_card("RC", "receipts", "Past Receipts", "Find \u2022 Reprint \u2022 Share", INFO, height=108)
        past.bind(on_release=lambda *_: Clock.schedule_once(lambda dt: setattr(self.manager, "current", "receipts"), 0))
        layout.add_widget(past)
        note = Card(orientation="vertical", size_hint_y=None, padding=dp(14), shadow=False)
        note.bind(minimum_height=note.setter("height"))
        note.add_widget(wrap_label("Routine expenses are recorded from the cashier screen and included in the existing settlement system.",
                                   font_size=sp(12), color=TEXT_MUTED))
        layout.add_widget(note)
        self.set_content(layout)


class Capital(Base):
    """Owner's capital. Every figure comes from the finance engine, so this screen, Live Today,
    the statements and the Business Capital dashboard always agree."""

    def on_pre_enter(self, *_):
        self.clear_widgets()
        db = self.manager.app.db
        c = fin_compute(db)
        p = c["position"]
        ok = c["setup_done"]
        layout = BoxLayout(orientation="vertical", padding=dp(8), spacing=dp(6))
        layout.add_widget(self.top("Capital / Net Worth"))
        layout.add_widget(AppLabel(text=self.shop_name(), bold=True, font_size=sp(18), size_hint_y=None, height=dp(32)))
        headline = Card(orientation="vertical", padding=dp(8), size_hint_y=None, height=dp(78))
        headline.add_widget(AppLabel(text="NET BUSINESS CAPITAL (assets - liabilities)" if ok else "CAPITAL ESTIMATE (setup incomplete)", font_size=sp(12), size_hint_y=None, height=dp(24)))
        headline.add_widget(AppLabel(text=fin_fmt(p["net_capital"] if ok else p["ending_equity"]), bold=True, font_size=sp(26)))
        layout.add_widget(headline)
        sw = starting_worth(db)
        layout.add_widget(AppLabel(text="WORTH WHEN YOU STARTED: " + fin_fmt(sw["worth"]) + "   (opening stock " + fin_fmt(sw["inventory"]) + ")",
                                   bold=True, font_size=sp(12), size_hint_y=None, height=dp(26)))
        layout.add_widget(AppLabel(text="Stock added before your first sale is opening stock. Add equipment under Capital & Finance > Record a transaction.",
                                   font_size=sp(10), size_hint_y=None, height=dp(20)))
        font = mono_font()
        view = AppTextInput(readonly=True, multiline=True, font_size=sp(12), **({"font_name": font} if font else {}))
        retail = sum(max(0.0, safe_float(x.get("qty"))) * max(0.0, safe_float(x.get("sell"))) for x in db.products)
        view.text = fin_investment_text(db) + "\n\n" + fin_report_text(c, "ALL TIME") + "\n\n" + "\n".join([
            "STOCK AT SELLING PRICE (info only)", "-" * FIN_W,
            _lr("Stock at selling prices", num(retail), FIN_W), _lr("Potential margin in stock", num(retail - p["inventory_physical"]), FIN_W),
            "Potential margin is not profit until sold."])
        self.autosize_text(view, dp(500))
        layout.add_widget(view)
        grid = GridLayout(cols=2, spacing=dp(6), size_hint_y=None, height=dp(152))
        for text, kind, color in (("ADD EQUIPMENT / ASSET", "equipment", PRIMARY_SOFT),
                                  ("OWNER WITHDRAWAL", "withdraw", DANGER), ("FULL DASHBOARD", None, INFO)):
            b = AppButton(text=text, font_size=sp(12), background_color=color, size_hint_y=None, height=dp(46))
            if kind:
                b.bind(on_release=lambda _b, k=kind: fin_open_form(self, k))
            else:
                b.bind(on_release=lambda *_: setattr(self.manager, "current", "finance"))
            grid.add_widget(b)
        layout.add_widget(grid)
        layout.add_widget(AppLabel(text="OWNER MONEY HISTORY (newest first)", bold=True, size_hint_y=None, height=dp(30)))
        hist = [r for r in fin_journal(db) if r["category"].startswith("Owner")]
        if not hist:
            layout.add_widget(AppLabel(text="No investments or withdrawals recorded yet.", size_hint_y=None, height=dp(36), font_size=sp(12)))
        for r in hist[:60]:
            when = parse_record_datetime(r["date"])
            stamp = when.strftime("%d/%m/%Y %H:%M") if when else "?"
            row = AppLabel(text=f"{stamp}   {r['category']}   {fin_fmt(r['amount'])}   {r['method']}" + ((" - " + r["ref"]) if r["ref"] else ""),
                           font_size=sp(11), size_hint_y=None, height=dp(28), halign="left", valign="middle")
            row.bind(width=lambda inst, w: setattr(inst, "text_size", (w, None)))
            layout.add_widget(row)
        self.set_content(layout)


class ReplacementPlan(Base):
    """Equipment Replacement Plan. A saving plan only: it never changes cash, capital or profit.
    Plain words on purpose (shop owners with little schooling): what to put aside, what you have put aside."""

    def _para(self, layout, text, size=12, bold=False, color=None, height=None):
        lab = AppLabel(text=text, font_size=sp(size), bold=bold, halign="left", valign="middle",
                       size_hint_y=None, height=height or dp(size * 2 + 6), **({"color": color} if color else {}))
        lab.bind(width=lambda i, w: setattr(i, "text_size", (w, None)))
        lab.bind(texture_size=lambda i, ts: setattr(i, "height", max(height or dp(size * 2 + 6), ts[1] + dp(8))))
        layout.add_widget(lab)
        return lab

    def _line(self, left, right="", bold=False, size=12, left_width=.5):
        row = BoxLayout(orientation="horizontal", size_hint_y=None, height=dp(24))
        for text, hint, align in ((left, left_width, "left"), (right, 1 - left_width, "right")):
            lab = AppLabel(text=text, bold=bold, font_size=sp(size), halign=align, valign="middle",
                           size_hint_x=hint, shorten=True, shorten_from="right")
            lab.bind(size=lambda inst, s: setattr(inst, "text_size", s))
            row.add_widget(lab)
        return row

    def on_pre_enter(self, *_):
        self.clear_widgets()
        db = self.manager.app.db
        plan = fin_replacement(db)
        layout = BoxLayout(orientation="vertical", padding=dp(8), spacing=dp(6))
        layout.add_widget(self.top("Equipment Replacement Plan"))
        layout.add_widget(AppLabel(text=self.shop_name(), bold=True, font_size=sp(18), size_hint_y=None, height=dp(32)))
        self._para(layout, "This is a SAVING PLAN. It does not take any money out of your business. "
                           "Your real money is in Business Capital.", 11, color=TEXT_MUTED)
        self._para(layout, "As at " + plan["as_of"].strftime("%d/%m/%Y"), 11, color=TEXT_MUTED, height=dp(24))
        if not plan["assets"]:
            self._para(layout, "No equipment recorded yet. Add shelves, fridge, scale and so on with "
                               "Capital & Finance > Record a transaction > Add equipment / asset.", 12)
            self._history(layout, db)
            self.set_content(layout)
            return

        # ---- the answer, in three lines
        card = Card(orientation="vertical", padding=dp(10), spacing=dp(4), size_hint_y=None, height=dp(232))
        card.add_widget(AppLabel(text="PUT ASIDE EVERY DAY", font_size=sp(12), bold=True, size_hint_y=None, height=dp(22)))
        card.add_widget(AppLabel(text=fin_fmt(plan["per_day_total"]), font_size=sp(26), bold=True, size_hint_y=None, height=dp(40)))
        for left, value in (("You should have put aside by now", fin_fmt(plan["should_have_total"])),
                            ("You have put aside", fin_fmt(plan["saved_total"]))):
            card.add_widget(self._line(left, value, size=12, left_width=.62))
        gap = plan["gap"]
        if gap > 0.5:
            verdict, color = "NOT ENOUGH YET. You are short by " + fin_fmt(gap), DANGER
        else:
            verdict, color = "GOOD. You have put aside enough" + ((" (" + fin_fmt(-gap) + " extra)") if gap < -0.5 else ""), SUCCESS
        v = AppLabel(text=verdict, font_size=sp(14), bold=True, color=color, halign="left", valign="middle",
                     size_hint_y=None, height=dp(52))
        v.bind(width=lambda i, w: setattr(i, "text_size", (w, None)))
        card.add_widget(v)
        card.add_widget(AppLabel(text="Replacing everything at today's cost: " + fin_fmt(plan["cost_total"]),
                                 font_size=sp(11), color=TEXT_MUTED, size_hint_y=None, height=dp(22)))
        layout.add_widget(card)

        rp = AppButton(text="REPLACE / UPGRADE EQUIPMENT", background_color=hexc("F2C94C"), color=TEXT_DARK,
                       font_size=sp(13), size_hint_y=None, height=dp(48))
        rp.bind(on_release=lambda *_: fin_open_form(self, "equipment_replace"))
        layout.add_widget(rp)
        row = BoxLayout(size_hint_y=None, height=dp(48), spacing=dp(6))
        add = AppButton(text="I PUT MONEY ASIDE", background_color=SUCCESS, font_size=sp(13))
        add.bind(on_release=lambda *_: self.add_saving())
        undo = AppButton(text="UNDO LAST", background_color=GREY, font_size=sp(13), size_hint_x=.4)
        undo.bind(on_release=lambda *_: self.undo_saving())
        row.add_widget(add); row.add_widget(undo)
        layout.add_widget(row)
        self._para(layout, "Keep the money you put aside somewhere safe, apart from the shop till.", 11, color=TEXT_MUTED)

        # ---- the equipment list
        layout.add_widget(AppLabel(text="MY EQUIPMENT", bold=True, font_size=sp(13), size_hint_y=None, height=dp(30)))
        for a in plan["assets"]:
            c = Card(orientation="vertical", padding=dp(8), spacing=dp(2), size_hint_y=None, height=dp(176))
            c.add_widget(AppLabel(text=a["name"], bold=True, font_size=sp(14), size_hint_y=None, height=dp(26)))
            if a["worn_out"]:
                status, scolor = "TIME TO REPLACE (planned life is over)", DANGER
            elif a["days_left"] <= 90:
                status, scolor = "Replace soon: about " + str(max(a["days_left"], 0)) + " days left", DANGER
            else:
                status, scolor = "Replace around " + a["replace_on"].strftime("%d/%m/%Y"), TEXT_MUTED
            c.add_widget(AppLabel(text=status, font_size=sp(11), color=scolor, size_hint_y=None, height=dp(22)))
            c.add_widget(self._line("Bought " + a["bought"].strftime("%d/%m/%Y") + " for", fin_fmt(a["cost"]), size=11, left_width=.5))
            c.add_widget(self._line("Put aside each day", "-" if a["worn_out"] else fin_fmt(a["per_day"]), size=11, bold=True, left_width=.5))
            c.add_widget(self._line("Should have by now", fin_fmt(a["should_have"]), size=11, left_width=.5))
            c.add_widget(self._line("Value left (estimate)", fin_fmt(a["value_now"]), size=11, left_width=.5))
            layout.add_widget(c)
        self._para(layout, "Value left is only an estimate: the cost minus the money you have put aside. "
                           "It is not counted in your Business Capital.", 10, color=TEXT_MUTED)

        self._history(layout, db)

        # ---- what the owner has put aside
        layout.add_widget(AppLabel(text="MONEY I PUT ASIDE (newest first)", bold=True, font_size=sp(13), size_hint_y=None, height=dp(30)))
        hist = list(reversed(replacement_savings(db)))
        if not hist:
            self._para(layout, "Nothing noted yet.", 11)
        for r in hist[:30]:
            when = parse_record_datetime(r.get("date"))
            stamp = when.strftime("%d/%m/%Y") if when else "?"
            layout.add_widget(self._line(stamp + ("  " + r["note"] if r.get("note") else ""), fin_fmt(r["amount"]), size=11, left_width=.6))
        self.set_content(layout)

    def _history(self, layout, db):
        reps = [e for e in live_ledger(getattr(db, "ledger", [])) if e.get("type") == "equipment_replacement"]
        if not reps:
            return
        layout.add_widget(AppLabel(text="EQUIPMENT I REPLACED (newest first)", bold=True, font_size=sp(13),
                                   size_hint_y=None, height=dp(30)))
        for e in sorted(reps, key=lambda x: str(x.get("date")), reverse=True)[:20]:
            when = parse_record_datetime(e.get("date"))
            oc, pr, nc = safe_float(e.get("old_cost")), safe_float(e.get("proceeds")), safe_float(e.get("amount"))
            diff = oc - pr
            c = Card(orientation="vertical", padding=dp(8), spacing=dp(2), size_hint_y=None, height=dp(152))
            c.add_widget(AppLabel(text=(when.strftime("%d/%m/%Y") if when else "?") + "  " + str(e.get("old_name") or "Equipment")
                                  + " -> " + str(e.get("note") or "New equipment"), bold=True, font_size=sp(12),
                                  size_hint_y=None, height=dp(26), shorten=True, shorten_from="right"))
            c.add_widget(self._line("Old cost", fin_fmt(oc), size=11, left_width=.55))
            c.add_widget(self._line("Sold for", fin_fmt(pr), size=11, left_width=.55))
            c.add_widget(self._line("Loss on sale" if diff >= 0 else "Gain on sale", fin_fmt(abs(diff)), size=11, bold=True, left_width=.55))
            c.add_widget(self._line("New equipment cost", fin_fmt(nc), size=11, left_width=.55))
            c.add_widget(self._line("Extra cash paid" if nc - pr >= 0 else "Cash left over", fin_fmt(abs(nc - pr)), size=11, left_width=.55))
            layout.add_widget(c)

    def add_saving(self):
        db = self.manager.app.db
        plan = fin_replacement(db)
        suggest = plan["per_day_total"]
        fin_form(self, "Money put aside",
                 "Type the money you really put aside for replacing equipment. Suggested each day: " + fin_fmt(suggest)
                 + ". This is only noted here. Your Business Capital does not change.",
                 [("amount", "How much did you put aside?", "amount", None), ("note", "Note (optional)", "text", "")],
                 lambda v, k: (replacement_add_saving(db, v["amount"], v["note"], k),
                               "Noted: " + fin_fmt(safe_float(v["amount"])) + " put aside.")[1])

    def undo_saving(self):
        db = self.manager.app.db
        rows = replacement_savings(db)
        if not rows:
            self.msg("Nothing to undo.")
            return
        last = rows[-1]
        box = BoxLayout(orientation="vertical", padding=dp(10), spacing=dp(8))
        box.add_widget(AppLabel(text="Remove the last note of " + fin_fmt(last["amount"]) + "? Your real money is not affected.",
                                font_size=sp(13)))
        yes = AppButton(text="YES, REMOVE IT", background_color=DANGER, size_hint_y=None, height=dp(46))
        no = AppButton(text="NO", background_color=GREY, size_hint_y=None, height=dp(42))
        box.add_widget(yes); box.add_widget(no)
        popup = Popup(title="Undo", content=box, size_hint=(.9, .4))

        def do(*_):
            replacement_undo_last(db)
            db.save()
            popup.dismiss()
            self.on_pre_enter()
        yes.bind(on_release=do)
        no.bind(on_release=lambda *_: popup.dismiss())
        popup.open()


class StockPurchases(Base):
    """Every time stock was bought, with its date. Adding or restocking a
    product on the Products screen logs an entry here automatically."""

    def on_pre_enter(self, *_):
        self._build_list(100)

    def _build_list(self, limit=100):
        self.clear_widgets()
        db = self.manager.app.db
        layout = BoxLayout(orientation="vertical", padding=dp(8), spacing=dp(5))
        layout.add_widget(self.top("Stock Purchase History"))
        entries = list(reversed(db.purchases))
        total = sum(safe_float(p.get("total_cost", 0)) for p in db.purchases)
        layout.add_widget(AppLabel(text=f"All-time stock purchased: {money(total)}", bold=True,
                                font_size=sp(14), size_hint_y=None, height=dp(34)))
        sup_btn = AppButton(text="Suppliers You Owe / Pay Supplier", size_hint_y=None, height=dp(46), background_color=INFO)
        sup_btn.bind(on_release=lambda *_: fin_debt_hub(self, "supplier"))
        layout.add_widget(sup_btn)
        if not entries:
            layout.add_widget(AppLabel(text="No stock purchases recorded yet. They are logged\nautomatically when you add or restock a product.",
                                    font_size=sp(12), size_hint_y=None, height=dp(50)))
        else:
            for p in entries[:limit]:
                when = parse_record_datetime(p.get("date"))
                stamp = when.strftime("%d/%m/%Y %H:%M") if when else "?"
                owed = safe_float(p.get("total_cost", 0)) - (safe_float(p.get("total_cost", 0)) if p.get("paid_amount") is None else safe_float(p.get("paid_amount")))
                text = (f"{stamp}\n{cap(p.get('product',''))}: "
                       f"{safe_float(p.get('qty',0)):g} {p.get('unit','')} "
                       f"@ {money(p.get('unit_cost',0))} = {money(p.get('total_cost',0))}"
                       + (f"  (CREDIT, owing {money(owed)} to {p.get('supplier') or 'supplier'})" if owed > 0.004 else ""))
                layout.add_widget(AppLabel(text=text, font_size=sp(12), size_hint_y=None, height=dp(52), halign="left"))
            if len(entries) > limit:
                more = AppButton(text="Show 100 older purchases (" + str(len(entries) - limit) + " not shown)",
                                 size_hint_y=None, height=dp(46), background_color=SLATE)
                more.bind(on_release=lambda *_: self._build_list(limit + 100))
                layout.add_widget(more)
        self.set_content(layout)


SHELF_FIELDS = ("department", "category", "product_class", "brand", "variant")

def product_shelf(p):
    """Folder path of a product. Old products without a saved folder are placed by their classification."""
    saved = p.get("shelf")
    if isinstance(saved, list):
        return [str(x).strip() for x in saved if str(x).strip()]
    path = []
    for k in SHELF_FIELDS:
        v = str(p.get(k) or "").strip()
        if v and not (path and path[-1].casefold() == v.casefold()):
            path.append(v)
    return path or ["Unsorted"]

def _cf(path):
    return [str(x).casefold() for x in path]

def path_startswith(path, prefix):
    return _cf(path)[:len(prefix)] == _cf(prefix)

def path_equal(a, b):
    return _cf(a) == _cf(b)

def unit_choices(db):
    extra = db.settings.get("custom_units", []) if isinstance(db.settings, dict) else []
    extra = [u for u in extra if isinstance(u, str) and u not in UNITS]
    return [u for u in UNITS if u != "Custom"] + extra + ["Custom", "Other"]

def department_choices(db):
    extra = db.settings.get("custom_departments", []) if isinstance(db.settings, dict) else []
    extra = [d for d in extra if isinstance(d, str) and d not in DEPARTMENTS]
    return [d for d in DEPARTMENTS if d != "Other"] + extra + ["Other"]

def remember_choice(db, key, value, builtin):
    v = str(value or "").strip()
    if not v or v.casefold() in [str(b).casefold() for b in builtin]:
        return
    lst = db.settings.get(key)
    if not isinstance(lst, list):
        lst = []
    if v.casefold() not in [str(x).casefold() for x in lst]:
        lst.append(v)
        db.settings[key] = lst


class Products(Base):
    """Folder-style inventory browser: browse shelves until the final product list."""
    FOLDER_LEVELS = [
        ("department", "Departments"),
        ("category", "Categories"),
        ("product_class", "Product classes"),
        ("brand", "Brands"),
        ("variant", "Types / sizes"),
    ]

    SCREEN_TITLE = "Products / Inventory"

    # ------------------------------------------------------------------ data helpers
    def on_pre_enter(self, *_):
        if not hasattr(self, "browse_path"):
            self.browse_path = []
        self.select_mode = False
        self.selected = set()
        self.render_folder_browser()

    def _db(self):
        return self.manager.app.db

    def _store(self):
        db = self._db()
        if not isinstance(getattr(db, "shelf_folders", None), list):
            db.shelf_folders = []
        return db.shelf_folders

    def _children(self, path):
        names = {}
        for p in self._db().products:
            sp = product_shelf(p)
            if len(sp) > len(path) and path_startswith(sp, path):
                names.setdefault(sp[len(path)].casefold(), sp[len(path)])
        for sp in self._store():
            if isinstance(sp, list) and len(sp) > len(path) and path_startswith(sp, path):
                names.setdefault(str(sp[len(path)]).casefold(), str(sp[len(path)]))
        return sorted(names.values(), key=str.casefold)

    def _products_at(self, path):
        return [p for p in self._db().products if path_equal(product_shelf(p), path)]

    def _products_under(self, path):
        return [p for p in self._db().products if path_startswith(product_shelf(p), path)]

    def _commit(self):
        self._db().save()

    def _rewrite_prefix(self, old, new, keep_new=True):
        """Move everything stored under folder path `old` so it lives under `new`."""
        db = self._db()
        n = len(old)
        for p in db.products:
            sp = product_shelf(p)
            if path_startswith(sp, old):
                p["shelf"] = list(new) + sp[n:]
        out = []
        for f in self._store():
            if not isinstance(f, list):
                continue
            if path_startswith(f, old):
                f = list(new) + list(f)[n:]
            out.append(list(f))
        if keep_new and new:
            out.append(list(new))
        seen, clean = set(), []
        for f in out:
            key = tuple(_cf(f))
            if f and key not in seen:
                seen.add(key)
                clean.append(f)
        db.shelf_folders = clean

    def _item_key_for_product(self, p):
        return ("p", id(p))

    def _selected_items(self):
        folders = [list(self.browse_path) + [k[1]] for k in self.selected if k[0] == "f"]
        ids = {k[1] for k in self.selected if k[0] == "p"}
        prods = [p for p in self._db().products if id(p) in ids]
        return folders, prods

    # ------------------------------------------------------------------ screen
    def render_folder_browser(self):
        self.clear_widgets()
        path = self.browse_path
        root = BoxLayout(orientation="vertical", padding=dp(8), spacing=dp(6))
        root.add_widget(self.top(self.SCREEN_TITLE))

        nav = BoxLayout(size_hint_y=None, height=dp(44), spacing=dp(5))
        home = AppButton(text="⌂", size_hint_x=None, width=dp(48), font_size=sp(20), background_color=TEAL, disabled=not path)
        home.bind(on_release=lambda *_: self._go(None))
        crumb = AppLabel(text="Shop" + "".join("  ›  " + p for p in path), bold=True, font_size=sp(13),
                         halign="left", valign="middle", color=PRIMARY_DARK, shorten=True, shorten_from="left")
        crumb.bind(size=lambda i, v: setattr(i, "text_size", (v[0], v[1])))
        nav.add_widget(home); nav.add_widget(crumb)
        root.add_widget(nav)

        tools = BoxLayout(size_hint_y=None, height=dp(44), spacing=dp(5))
        if self.select_mode:
            n = len(self.selected)
            lab = AppLabel(text=f"{n} selected", bold=True, font_size=sp(14), color=PRIMARY_DARK)
            all_btn = AppButton(text="SELECT ALL", background_color=INFO, size_hint_x=None, width=dp(110), font_size=sp(12))
            done = AppButton(text="DONE", background_color=GREY, size_hint_x=None, width=dp(80), font_size=sp(12))
            all_btn.bind(on_release=lambda *_: self._select_all())
            done.bind(on_release=lambda *_: self._exit_select())
            tools.add_widget(lab); tools.add_widget(all_btn); tools.add_widget(done)
        else:
            nf = AppButton(text="＋ FOLDER", background_color=ACCENT, font_size=sp(13))
            ap = AppButton(text="＋ PRODUCT", background_color=SUCCESS, font_size=sp(13))
            sel = AppButton(text="☑ SELECT", background_color=PRIMARY, font_size=sp(13))
            nf.bind(on_release=lambda *_: self.new_folder())
            ap.bind(on_release=self.add_product)
            sel.bind(on_release=lambda *_: self._enter_select())
            tools.add_widget(nf); tools.add_widget(ap); tools.add_widget(sel)
        root.add_widget(tools)

        scroll = SmoothScroll(do_scroll_x=False, bar_width=dp(5))
        box = BoxLayout(orientation="vertical", size_hint_y=None, spacing=dp(6), padding=(0, dp(4)))
        box.bind(minimum_height=box.setter("height"))
        folders = self._children(path)
        prods = sorted(self._products_at(path),
                       key=lambda p: (str(p.get("name", "")).casefold(), str(p.get("variant", "")).casefold()))
        if not folders and not prods:
            msg = ("This folder is empty.\nTap ＋ FOLDER to make a folder, or ＋ PRODUCT to add stock here."
                   if path else "Your shelves are empty.\nTap ＋ PRODUCT to add stock, or ＋ FOLDER to make a folder.")
            lbl = AppLabel(text=msg, size_hint_y=None, height=dp(90), halign="center", valign="middle")
            lbl.bind(size=lambda i, v: setattr(i, "text_size", (v[0], v[1])))
            box.add_widget(lbl)
        for name in folders:
            fp = list(path) + [name]
            count = len(self._products_under(fp))
            subs = len(self._children(fp))
            sub_text = f"{count} item{'s' if count != 1 else ''}" + (f"  ·  {subs} folder{'s' if subs != 1 else ''}" if subs else "")
            key = ("f", name)
            row = FileRow("📁", name, sub_text, accent=FOLDER_GOLD, selected=key in self.selected, show_check=self.select_mode,
                          on_tap=lambda k=key, n=name: self._tap_folder(k, n),
                          on_long=lambda k=key: self._long_press(k))
            box.add_widget(row)
        for p in prods:
            detail = " · ".join(v for v in [str(p.get("brand") or "").strip(), str(p.get("variant") or "").strip()] if v)
            title = str(p.get("name") or "Unnamed product") + (f" — {detail}" if detail else "")
            sub = f"Stock {safe_float(p.get('qty', 0)):g} {p.get('unit', 'Piece')}   |   Sell {money(p.get('sell', 0))}   |   Buy {money(p.get('buy', 0))}"
            key = ("p", id(p))
            row = FileRow("📦", title, sub, accent=TEAL, selected=key in self.selected, show_check=self.select_mode,
                          on_tap=lambda k=key, pr=p: self._tap_product(k, pr),
                          on_long=lambda k=key: self._long_press(k))
            box.add_widget(row)
        scroll.add_widget(box)
        root.add_widget(scroll)

        if self.select_mode:
            n = len(self.selected)
            bar = GridLayout(cols=3, spacing=dp(5), size_hint_y=None, height=dp(48))
            mv = AppButton(text="MOVE", background_color=INFO, disabled=n == 0)
            only = list(self.selected)[0] if n == 1 else None
            ed = AppButton(text=("RENAME" if only and only[0] == "f" else "EDIT"), background_color=ACCENT, disabled=n != 1)
            dl = AppButton(text="DELETE", background_color=DANGER, disabled=n == 0)
            mv.bind(on_release=lambda *_: self.move_selected())
            ed.bind(on_release=lambda *_: self.edit_selected())
            dl.bind(on_release=lambda *_: self.delete_selected())
            bar.add_widget(mv); bar.add_widget(ed); bar.add_widget(dl)
            root.add_widget(bar)
        self.add_widget(root)

    # ------------------------------------------------------------------ navigation / selection
    def go_back(self, *_):
        """Back (top bar or phone key) steps out of select mode, then up one folder, then leaves the screen."""
        if getattr(self, "select_mode", False):
            self._exit_select()
            return
        if getattr(self, "browse_path", None):
            self._go(self.browse_path[:-1])
            return
        super().go_back()

    def _go(self, path):
        self.browse_path = list(path or [])
        self.select_mode = False
        self.selected = set()
        self.render_folder_browser()

    def _enter_select(self):
        self.select_mode = True
        self.selected = set()
        self.render_folder_browser()

    def _exit_select(self):
        self.select_mode = False
        self.selected = set()
        self.render_folder_browser()

    def _select_all(self):
        keys = {("f", n) for n in self._children(self.browse_path)}
        keys |= {("p", id(p)) for p in self._products_at(self.browse_path)}
        self.selected = keys
        self.render_folder_browser()

    def _long_press(self, key):
        def go(_dt):
            self.select_mode = True
            self.selected = {key}
            self.render_folder_browser()
        Clock.schedule_once(go, 0)

    def _toggle(self, key):
        if key in self.selected:
            self.selected.discard(key)
        else:
            self.selected.add(key)
        self.render_folder_browser()

    def _tap_folder(self, key, name):
        if self.select_mode:
            self._toggle(key)
        else:
            self._go(list(self.browse_path) + [name])

    def _tap_product(self, key, product):
        if self.select_mode:
            self._toggle(key)
        else:
            self.edit_product(product)

    def edit_selected(self):
        folders, prods = self._selected_items()
        if len(folders) == 1 and not prods:
            self.rename_folder(folders[0])
        elif len(prods) == 1 and not folders:
            self.edit_product(prods[0])

    # ------------------------------------------------------------------ small dialogs
    def ask_text(self, title, hint, initial, ok_text, on_ok):
        box = BoxLayout(orientation="vertical", padding=dp(10), spacing=dp(8))
        field = AppTextInput(text=initial, hint_text=hint, multiline=False, size_hint_y=None, height=dp(46))
        status = AppLabel(text="", size_hint_y=None, height=dp(24), font_size=sp(11), color=DANGER)
        row = GridLayout(cols=2, spacing=dp(6), size_hint_y=None, height=dp(46))
        ok = AppButton(text=ok_text, background_color=SUCCESS)
        cancel = AppButton(text="CANCEL", background_color=GREY)
        row.add_widget(ok); row.add_widget(cancel)
        box.add_widget(field); box.add_widget(status); box.add_widget(row)
        popup = Popup(title=title, content=box, size_hint=(.9, None), height=dp(220), auto_dismiss=False)

        def go(*_):
            err = on_ok(field.text.strip())
            if err:
                status.text = err
            else:
                popup.dismiss()
        ok.bind(on_release=go)
        field.bind(on_text_validate=go)
        cancel.bind(on_release=lambda *_: popup.dismiss())
        popup.open()
        Clock.schedule_once(lambda dt: setattr(field, "focus", True), 0.35)

    def confirm(self, title, text, ok_text, on_ok, ok_color=DANGER):
        box = BoxLayout(orientation="vertical", padding=dp(10), spacing=dp(8))
        lbl = AppLabel(text=text, halign="left", valign="middle", font_size=sp(13))
        lbl.bind(size=lambda i, v: setattr(i, "text_size", (v[0], None)))
        row = GridLayout(cols=2, spacing=dp(6), size_hint_y=None, height=dp(46))
        ok = AppButton(text=ok_text, background_color=ok_color)
        cancel = AppButton(text="CANCEL", background_color=GREY)
        row.add_widget(ok); row.add_widget(cancel)
        box.add_widget(lbl); box.add_widget(row)
        popup = Popup(title=title, content=box, size_hint=(.9, .45), auto_dismiss=False)
        ok.bind(on_release=lambda *_: (popup.dismiss(), on_ok()))
        cancel.bind(on_release=lambda *_: popup.dismiss())
        popup.open()

    def _name_problem(self, parent, name, ignore=None):
        if not name:
            return "Please type a folder name."
        if any(c in name for c in "/\\"):
            return "A folder name cannot contain / or \\"
        for existing in self._children(parent):
            if existing.casefold() == name.casefold() and (ignore is None or existing.casefold() != ignore.casefold()):
                return "A folder with this name already exists here."
        return ""

    # ------------------------------------------------------------------ folder operations
    def new_folder(self, parent=None, after=None):
        parent = list(self.browse_path if parent is None else parent)

        def ok(name):
            err = self._name_problem(parent, name)
            if err:
                return err
            self._store().append(parent + [name])
            self._commit()
            if after:
                after()
            else:
                self.render_folder_browser()
            return ""
        self.ask_text("New folder", "Folder name (e.g. Pens, Rice, Phones)", "", "CREATE", ok)

    def rename_folder(self, fp):
        old = fp[-1]
        parent = fp[:-1]

        def ok(name):
            if name == old:
                return ""
            err = self._name_problem(parent, name, ignore=old)
            if err:
                return err
            self._rewrite_prefix(fp, parent + [name])
            self._commit()
            self._exit_select()
            return ""
        self.ask_text("Rename folder", "New folder name", old, "SAVE", ok)

    def move_selected(self):
        folders, prods = self._selected_items()
        if folders or prods:
            self._move_popup(folders, prods)

    def _move_popup(self, folders, prods):
        state = {"path": list(self.browse_path)}
        box = BoxLayout(orientation="vertical", padding=dp(8), spacing=dp(6))
        count = len(folders) + len(prods)
        box.add_widget(AppLabel(text=f"Moving {count} item{'s' if count != 1 else ''}. Open the destination folder, then tap MOVE HERE.",
                                size_hint_y=None, height=dp(40), font_size=sp(12), halign="left", valign="middle"))
        box.children[0].bind(size=lambda i, v: setattr(i, "text_size", (v[0], v[1])))
        crumb = AppLabel(text="", bold=True, size_hint_y=None, height=dp(28), font_size=sp(13), halign="left",
                         valign="middle", color=PRIMARY_DARK, shorten=True, shorten_from="left")
        crumb.bind(size=lambda i, v: setattr(i, "text_size", (v[0], v[1])))
        box.add_widget(crumb)
        nav = BoxLayout(size_hint_y=None, height=dp(42), spacing=dp(5))
        top_btn = AppButton(text="⌂ TOP", background_color=TEAL, font_size=sp(12))
        new_btn = AppButton(text="＋ NEW FOLDER", background_color=ACCENT, font_size=sp(12))
        nav.add_widget(top_btn); nav.add_widget(new_btn)
        box.add_widget(nav)
        listing = BoxLayout(orientation="vertical", size_hint_y=None, spacing=dp(5))
        listing.bind(minimum_height=listing.setter("height"))
        sc = SmoothScroll(do_scroll_x=False, bar_width=dp(4))
        sc.add_widget(listing)
        box.add_widget(sc)
        row = GridLayout(cols=2, spacing=dp(6), size_hint_y=None, height=dp(46))
        here = AppButton(text="MOVE HERE", background_color=SUCCESS)
        cancel = AppButton(text="CANCEL", background_color=GREY)
        row.add_widget(here); row.add_widget(cancel)
        box.add_widget(row)
        popup = Popup(title="Move to…", content=box, size_hint=(.94, .86), auto_dismiss=False)

        def refresh():
            crumb.text = "Destination:  Shop" + "".join("  ›  " + p for p in state["path"])
            top_btn.disabled = not state["path"]
            listing.clear_widgets()
            shown = 0
            for name in self._children(state["path"]):
                full = state["path"] + [name]
                if any(path_startswith(full, fp) for fp in folders):
                    continue  # cannot move a folder into itself
                shown += 1
                n = len(self._products_under(full))
                listing.add_widget(FileRow("📁", name, f"{n} item{'s' if n != 1 else ''}", accent=FOLDER_GOLD,
                                           on_tap=lambda nm=name: (state["path"].append(nm), refresh())))
            if not shown:
                l = AppLabel(text="No folders here. Tap MOVE HERE to place items in this folder, or ＋ NEW FOLDER.",
                             size_hint_y=None, height=dp(70), font_size=sp(12), halign="center", valign="middle")
                l.bind(size=lambda i, v: setattr(i, "text_size", (v[0], v[1])))
                listing.add_widget(l)

        def go_top(*_):
            state["path"] = []
            refresh()

        def go_up(*_):
            state["path"] = state["path"][:-1]
            refresh()

        def make_new(*_):
            self.new_folder(parent=state["path"], after=refresh)

        def do_move(*_):
            dest = list(state["path"])
            for fp in folders:
                if path_startswith(dest, fp):
                    self.msg("A folder cannot be moved into itself.")
                    return
            for fp in folders:
                self._rewrite_prefix(fp, dest + [fp[-1]])
            for p in prods:
                p["shelf"] = list(dest)
            self._commit()
            popup.dismiss()
            self._exit_select()

        top_btn.bind(on_release=go_top)
        new_btn.bind(on_release=make_new)
        here.bind(on_release=do_move)
        cancel.bind(on_release=lambda *_: popup.dismiss())
        popup._on_back = lambda: (go_up() if state["path"] else popup.dismiss())   # phone Back: up a folder, then close
        refresh()
        popup.open()

    def delete_selected(self):
        folders, prods = self._selected_items()
        if not folders and not prods:
            return
        lines = []
        for fp in folders:
            n = len(self._products_under(fp))
            subs = len(self._children(fp))
            if n or subs:
                dest = "the parent folder" if len(fp) > 1 else "the top level"
                lines.append(f"• Folder “{fp[-1]}” will be removed. Its {n} product{'s' if n != 1 else ''}" +
                             (f" and {subs} sub-folder{'s' if subs != 1 else ''}" if subs else "") +
                             f" are kept and moved to {dest}.")
            else:
                lines.append(f"• Empty folder “{fp[-1]}” will be removed.")
        if prods:
            lines.append(f"• {len(prods)} product{'s' if len(prods) != 1 else ''} will be deleted permanently "
                         "(past sales and receipts are not affected).")
        lines.append("\nTip: use MOVE first if you want contents to go somewhere else.")

        def do():
            for fp in folders:
                self._rewrite_prefix(fp, fp[:-1], keep_new=False)
            gone = {id(p) for p in prods}
            db = self._db()
            fin_writeoff_deleted(db, [p for p in db.products if id(p) in gone])
            db.products[:] = [p for p in db.products if id(p) not in gone]
            self._commit()
            self._exit_select()
        self.confirm("Delete selected?", "\n".join(lines), "DELETE", do)

    # ------------------------------------------------------------------ product editor
    def edit_product(self, product):
        db = self._db()
        layout = BoxLayout(orientation="vertical", padding=dp(8), spacing=dp(5), size_hint_y=None)
        layout.bind(minimum_height=layout.setter("height"))

        def field(label, value, hint="", numeric=False):
            layout.add_widget(AppLabel(text=label, size_hint_y=None, height=dp(22), font_size=sp(11), halign="left", bold=True))
            lbl = layout.children[0]
            lbl.bind(size=lambda i, v: setattr(i, "text_size", (v[0], v[1])))
            w = AppTextInput(text=str(value), hint_text=hint, multiline=False, size_hint_y=None, height=dp(44),
                             **({"input_filter": "float"} if numeric else {}))
            layout.add_widget(w)
            return w

        name = field("Product name", product.get("name", ""), "Product name")
        sell = field("Selling price (per unit)", product.get("sell", 0), "Selling price", True)
        buy = field("Buying cost (per unit)", round(safe_float(product.get("buy", 0)), 4), "Cost per unit", True)
        brand = field("Brand", product.get("brand", ""), "Brand (optional)")
        variant = field("Size / type", product.get("variant", ""), "Size / type / variant")
        pclass = field("Product class", product.get("product_class", ""), "Product class")
        layout.add_widget(AppLabel(text="Stock unit", size_hint_y=None, height=dp(22), font_size=sp(11), halign="left", bold=True))
        unit = ChoicePicker(text=str(product.get("unit") or "Piece"), values=unit_choices(db), hint="Type your own unit")
        layout.add_widget(unit)
        where = "Shop" + "".join("  ›  " + p for p in product_shelf(product))
        loc = AppLabel(text="Folder:  " + where, size_hint_y=None, height=dp(34), font_size=sp(12), halign="left",
                       valign="middle", color=PRIMARY_DARK)
        loc.bind(size=lambda i, v: setattr(i, "text_size", (v[0], v[1])))
        layout.add_widget(loc)
        status = AppLabel(text="", size_hint_y=None, height=dp(24), font_size=sp(11), color=DANGER)
        layout.add_widget(status)
        row1 = GridLayout(cols=2, spacing=dp(6), size_hint_y=None, height=dp(46))
        save = AppButton(text="SAVE CHANGES", background_color=SUCCESS)
        move = AppButton(text="MOVE TO FOLDER", background_color=INFO)
        row1.add_widget(save); row1.add_widget(move)
        row2 = GridLayout(cols=2, spacing=dp(6), size_hint_y=None, height=dp(46))
        delete = AppButton(text="DELETE PRODUCT", background_color=DANGER)
        close = AppButton(text="CLOSE", background_color=GREY)
        row2.add_widget(delete); row2.add_widget(close)
        layout.add_widget(row1); layout.add_widget(row2)
        popup = Popup(title="Edit product", content=self.scroll_wrap(layout), size_hint=(.96, .92))

        def do_save(*_):
            try:
                new_name = name.text.strip()
                if not new_name:
                    raise ValueError("Product name is required.")
                if not unit.text.strip():
                    raise ValueError("Type your own unit or choose one from the list.")
                new_sell, new_buy = safe_float(sell.text), safe_float(buy.text)
                if new_sell < 0 or new_buy < 0:
                    raise ValueError("Prices cannot be negative.")
                key = (normalize_product_name(new_name), normalize_product_name(brand.text),
                       normalize_product_name(variant.text), normalize_product_name(pclass.text))
                for other in db.products:
                    if other is product:
                        continue
                    if (normalize_product_name(other.get("name", "")), normalize_product_name(other.get("brand", "")),
                            normalize_product_name(other.get("variant", "")), normalize_product_name(other.get("product_class", ""))) == key:
                        raise ValueError("Another product already has this name, brand, size and class.")
                old_buy = safe_float(product.get("buy", 0))
                product["name"] = new_name
                product["sell"] = new_sell
                product["buy"] = new_buy
                # A cost correction changes inventory value: record it as a traceable adjustment instead of
                # letting the value change silently (it flows through profit and reconciles with the stock).
                delta_value = safe_float(product.get("qty", 0)) * (new_buy - old_buy)
                if abs(delta_value) >= 0.005:
                    fin_ensure(db)
                    fin_post(db, {"type": "inventory_adjustment", "amount": delta_value, "product_pid": product.get("pid", ""),
                                  "product": new_name,
                                  "note": f"Unit cost of {new_name} changed from {old_buy:.2f} to {new_buy:.2f}"})
                product["brand"] = brand.text.strip()
                product["variant"] = variant.text.strip()
                product["product_class"] = pclass.text.strip() or "Other products"
                product["unit"] = unit.text.strip()
                if "shelf" not in product:
                    product["shelf"] = product_shelf(product)
                remember_choice(db, "custom_units", product["unit"], UNITS + ["Other"])
                self._commit()
                popup.dismiss()
                self.render_folder_browser()
            except Exception as e:
                status.text = str(e)

        def do_move(*_):
            popup.dismiss()
            self._move_popup([], [product])

        def do_delete(*_):
            def go():
                popup.dismiss()
                fin_writeoff_deleted(db, [product])
                db.products[:] = [p for p in db.products if p is not product]
                self._commit()
                self.render_folder_browser()
            self.confirm("Delete product?", f"Delete “{product.get('name', '')}” permanently?\n"
                         "Past sales and receipts are not affected.", "DELETE", go)

        save.bind(on_release=do_save)
        move.bind(on_release=do_move)
        delete.bind(on_release=do_delete)
        close.bind(on_release=lambda *_: popup.dismiss())
        popup.open()

    def add_product(self, *_):
        db = self.manager.app.db
        layout = BoxLayout(orientation="vertical", padding=dp(8), spacing=dp(5), size_hint_y=None)
        layout.bind(minimum_height=layout.setter("height"))

        name = AppTextInput(hint_text="Search or enter product name with size (e.g. Movit Herbal Jelly 30 g)",
                            multiline=False, size_hint_y=None, height=dp(44))
        layout.add_widget(name)
        name_match_hint = AppLabel(text="Type to search stock. Tap a suggestion to restock that exact item; leave it unselected to add a new product.",
                                   font_size=sp(11), size_hint_y=None, height=dp(48), halign="left", valign="middle")
        name_match_hint.bind(width=lambda inst, w: setattr(inst, "text_size", (w, None)))
        layout.add_widget(name_match_hint)
        suggestions = BoxLayout(orientation="vertical", size_hint_y=None, spacing=dp(3))
        suggestions.bind(minimum_height=suggestions.setter("height"))
        layout.add_widget(suggestions)
        selected = {"product": None, "setting": False}

        # Products are filed by FOLDER: the folder you are inside when you add the product (or "Unsorted" at the top level,
        # from where you can move it). The old Department / Category / Class / Brand / Size boxes are no longer needed:
        # put the size in the name (e.g. "Movit Herbal Jelly 30 g").
        folder_path = list(self.browse_path) if self.browse_path else []
        category = type("FolderCategory", (), {"text": (folder_path[0] if folder_path else "Other")})()   # top folder = category for filters/reports
        folder_label = AppLabel(text="Saved in folder: " + (" > ".join(folder_path) if folder_path else "Unsorted  (open a folder first to save straight into it, or move the product later)"),
                                font_size=sp(12), bold=True, size_hint_y=None, height=dp(40), halign="left", valign="middle")
        folder_label.bind(width=lambda inst, w: setattr(inst, "text_size", (w, None)))
        layout.add_widget(folder_label)

        total_cost = AppTextInput(hint_text="TOTAL purchase cost for this stock", multiline=False, input_filter="float", size_hint_y=None, height=dp(44))
        sell = AppTextInput(hint_text="Selling price PER UNIT", multiline=False, input_filter="float", size_hint_y=None, height=dp(44))
        quantity = AppTextInput(hint_text="Quantity stocked", multiline=False, input_filter="float", size_hint_y=None, height=dp(44))
        for label, widget in [("Total cost for this stock", total_cost), ("Selling price per unit", sell), ("Quantity", quantity)]:
            layout.add_widget(AppLabel(text=label, size_hint_y=None, height=dp(22), font_size=sp(11), halign="left"))
            layout.add_widget(widget)
        unit = ChoicePicker(text="Piece", values=unit_choices(db), hint="Type your own unit (e.g. Crate, Sachet, Yard)")
        layout.add_widget(AppLabel(text="Stock unit", size_hint_y=None, height=dp(22), font_size=sp(11), halign="left"))
        layout.add_widget(unit)
        paid_now = AppTextInput(hint_text="Amount paid now (empty = paid in full)", multiline=False, input_filter="float", size_hint_y=None, height=dp(44))
        supplier = AppTextInput(hint_text="Supplier name (required if part/unpaid)", multiline=False, size_hint_y=None, height=dp(44))
        pay_method = AppSpinner(text="cash", values=CASH_ACCOUNTS, size_hint_y=None, height=dp(44))
        for label, widget in [("Paid now (leave empty if paid in full; 0 = all on credit)", paid_now), ("Supplier", supplier), ("Paid from", pay_method)]:
            layout.add_widget(AppLabel(text=label, size_hint_y=None, height=dp(22), font_size=sp(11), halign="left"))
            layout.add_widget(widget)
        layout.add_widget(AppLabel(text="Tip: write the size in the name (e.g. Movit Herbal Jelly 30 g). Similar names are only suggestions; tap one to restock it.",
                                   font_size=sp(11), size_hint_y=None, height=dp(42), halign="left", valign="middle"))
        save = AppButton(text="SAVE / RESTOCK PRODUCT", size_hint_y=None, height=dp(46))
        layout.add_widget(save)

        def select_existing(product):
            selected["setting"] = True
            selected["product"] = product
            name.text = str(product.get("name") or "")
            folder_label.text = "Folder: " + " > ".join(product_shelf(product))
            unit_value = str(product.get("unit") or "Piece")
            if unit_value not in unit.values:
                unit.values = tuple(list(unit.values) + [unit_value])
            unit.text = unit_value
            sell.text = str(product.get("sell", ""))
            name_match_hint.text = "SELECTED EXISTING ITEM: stock will be added to this exact product."
            suggestions.clear_widgets()
            selected["setting"] = False

        def update_name_matches(_field, typed):
            if not selected["setting"]:
                selected["product"] = None
            suggestions.clear_widgets()
            query = normalize_product_name(typed)
            if not query:
                name_match_hint.text = "Type to search stock. Tap a suggestion to restock that exact item; leave it unselected to add a new product."
                return
            ranked = []
            for product in db.products:
                existing_name = str(product.get("name", "")).strip()
                searchable = " ".join(str(product.get(k) or "") for k in ("name", "brand", "variant", "product_class", "department", "category"))
                norm = normalize_product_name(searchable)
                if not norm:
                    continue
                ratio = difflib.SequenceMatcher(None, query, norm).ratio()
                typed_tokens = re.findall(r"[a-z0-9]+", str(typed).casefold())
                existing_tokens = re.findall(r"[a-z0-9]+", searchable.casefold())
                token_ratio = max([difflib.SequenceMatcher(None, a, b).ratio()
                                   for a in typed_tokens for b in existing_tokens] or [0])
                if query in norm or norm in query or ratio >= 0.48 or token_ratio >= 0.70:
                    score = max(ratio, token_ratio, 1.0 if query == normalize_product_name(existing_name) else 0)
                    ranked.append((score, product))
            ranked.sort(key=lambda pair: (-pair[0], str(pair[1].get("name", "")).casefold()))
            if not ranked:
                name_match_hint.text = "No close match found. You can add this as a new product."
                return
            name_match_hint.text = "POSSIBLE EXISTING ITEMS — tap the correct one to restock it."
            for score, product in ranked[:5]:
                details = " · ".join(v for v in [str(product.get("brand") or "").strip(), str(product.get("variant") or "").strip(), ("" if str(product.get("product_class") or "").strip().casefold() == "other products" else str(product.get("product_class") or "").strip())] if v) or " > ".join(product_shelf(product))
                label = str(product.get("name") or "Unnamed") + ("  |  " + details if details else "") + f"  |  Stock {safe_float(product.get('qty', 0)):g}"
                suggestion = AppButton(text=label, size_hint_y=None, height=dp(38), font_size=sp(11))
                suggestion.bind(on_release=lambda _btn, p=product: select_existing(p))
                suggestions.add_widget(suggestion)

        def clear_selection_if_identity_changed(_field, _value):
            if selected["setting"] or not selected.get("product"):
                return
            original = selected["product"]
            checks = [(unit, str(original.get("unit") or "Piece"))]
            if any(str(widget.text or "").strip().casefold() != old.strip().casefold() for widget, old in checks):
                selected["product"] = None
                name_match_hint.text = "Unit changed. Saving will create a separate product instead of restocking the selected item."

        name.bind(text=update_name_matches)
        for identity_widget in (unit,):
            identity_widget.bind(text=clear_selection_if_identity_changed)
        popup = Popup(title="Search, Add or Restock Product", content=self.scroll_wrap(layout), size_hint=(.96, .92))
        save.bind(on_release=lambda *_: self.save_product(name, total_cost, sell, quantity, category, unit, popup,
                                                          department=None, product_class=None,
                                                          brand=None, variant=None, selected_product=selected,
                                                          paid_now=paid_now, supplier=supplier, pay_method=pay_method))
        popup.open()

    def save_product(self, name, total_cost, sell, quantity, category, unit, popup,
                     department=None, product_class=None, brand=None, variant=None, selected_product=None,
                     paid_now=None, supplier=None, pay_method=None):
        if getattr(popup, "_saving", False):
            return   # a second tap / retry must not post the purchase twice
        try:
            product_name = name.text.strip()
            stock_cost = float(total_cost.text or 0)
            selling_price = float(sell.text or 0)
            qty = float(quantity.text or 0)
            if not product_name:
                raise ValueError("Product name is required.")
            if stock_cost < 0 or selling_price < 0:
                raise ValueError("Purchase and selling costs cannot be negative.")
            if qty <= 0:
                raise ValueError("Quantity must be greater than zero.")
            if department is not None and not str(department.text or "").strip():
                raise ValueError("Type your own department, or choose one from the list.")
            if not str(category.text or "").strip():
                raise ValueError("Type your own category, or choose one from the list.")
            if not str(unit.text or "").strip():
                raise ValueError("Type your own unit, or choose one from the list.")
            db = self.manager.app.db
            chosen = selected_product.get("product") if isinstance(selected_product, dict) else None
            product_department = str(department.text if department is not None else category.text)
            product_category = str(category.text or "Other")
            product_class_text = str(product_class.text or "").strip() if product_class is not None else ""
            brand_text = str(brand.text or "").strip() if brand is not None else ""
            variant_text = str(variant.text or "").strip() if variant is not None else ""
            unit_cost = stock_cost / qty
            paid_text = str(paid_now.text).strip() if paid_now is not None else ""
            paid_amount = stock_cost if paid_text == "" else float(paid_text)
            supplier_name = str(supplier.text).strip() if supplier is not None else ""
            if paid_amount < 0 or paid_amount > stock_cost + 0.004:
                raise ValueError("Amount paid now must be between 0 and the total cost.")
            if stock_cost - paid_amount > 0.004 and not supplier_name:
                raise ValueError("Enter the supplier's name when part or all of the stock is bought on credit.")
            method_name = str(pay_method.text) if pay_method is not None else "cash"
            new_shelf = list(self.browse_path) if self.browse_path else (product_shelf({
                "department": product_department, "category": product_category,
                "product_class": product_class_text, "brand": brand_text, "variant": variant_text}) if department is not None else ["Unsorted"])

            # Only a deliberate tap on a suggestion restocks an existing product.
            # Typo similarity never merges stock automatically.
            if chosen is None:
                _plain_class = lambda v: "" if normalize_product_name(v) == normalize_product_name("Other products") else normalize_product_name(v)
                key = (normalize_product_name(product_name), normalize_product_name(brand_text),
                       normalize_product_name(variant_text), _plain_class(product_class_text))
                exact = next((p for p in db.products if (
                    normalize_product_name(p.get("name", "")),
                    normalize_product_name(p.get("brand", "")),
                    normalize_product_name(p.get("variant", "")),
                    _plain_class(p.get("product_class", ""))) == key), None)
                if exact:
                    raise ValueError("This product already exists. Tap its suggestion above to add stock to the existing item, or change the name (e.g. add the size) to create a different product.")
                chosen = None

            is_new = chosen is None
            if not is_new:
                chosen["sell"] = selling_price
                # Keep selected item identity and classification; the user explicitly selected it.
                chosen.setdefault("department", chosen.get("category", product_department))
                if product_class_text: chosen["product_class"] = product_class_text
                if brand_text: chosen["brand"] = brand_text
                if variant_text: chosen["variant"] = variant_text
                saved_name = str(chosen.get("name") or product_name)
                saved_category = str(chosen.get("category") or product_category)
                saved_unit = str(chosen.get("unit") or unit.text)
            else:
                chosen = {"name": product_name, "buy": 0.0, "sell": selling_price, "qty": 0.0,
                          "category": product_category, "department": product_department,
                          "product_class": product_class_text or "Other products", "brand": brand_text,
                          "variant": variant_text, "unit": unit.text, "shelf": new_shelf,
                          "pid": "P-" + uuid.uuid4().hex[:16]}
                saved_name, saved_category, saved_unit = product_name, product_category, unit.text

            fin_ensure(db)
            popup._saving = True
            old_state = (safe_float(chosen.get("qty", 0)), safe_float(chosen.get("buy", 0)))
            try:
                # The engine decides everything else: weighted-average cost, paid/credit split, and whether this
                # is OPENING STOCK (first stock of a product, before the first sale) that counts towards the
                # shop's starting worth instead of being a cash purchase.
                capture_purchase(db, chosen, qty, stock_cost, supplier=supplier_name,
                                 paid_amount=paid_amount, category=saved_category)
            except Exception:
                popup._saving = False
                if not is_new:
                    chosen["qty"], chosen["buy"] = old_state
                raise
            if is_new:
                db.products.append(chosen)
            remember_choice(db, "custom_units", unit.text, UNITS + ["Other"])
            if department is not None:
                remember_choice(db, "custom_departments", product_department, DEPARTMENTS)
            if product_category.casefold() not in [str(c).casefold() for c in db.categories]:
                db.categories.append(product_category)
            db.save()
            popup.dismiss()
            self.on_pre_enter()
        except Exception as e:
            self.msg("Could not save product:\n" + str(e))

    def edit_price(self, product):
        """Admin price editor. This is intentionally a popup, not navigation back to another screen."""
        box = BoxLayout(orientation="vertical", padding=dp(8), spacing=dp(7))
        current = safe_float(product.get("sell", 0))
        field = AppTextInput(text=str(current), hint_text="New selling price per unit", multiline=False, input_filter="float", size_hint_y=None, height=dp(46))
        status = AppLabel(text="", size_hint_y=None, height=dp(35), font_size=sp(12))
        save = AppButton(text="SAVE SELLING PRICE", size_hint_y=None, height=dp(46))
        box.add_widget(AppLabel(text="Edit selling price: " + str(product.get("name", "")), bold=True, size_hint_y=None, height=dp(35)))
        box.add_widget(field); box.add_widget(status); box.add_widget(save)
        popup = Popup(title=self.shop_name() + " - Price Editor", content=self.scroll_wrap(box), size_hint=(.9, .4))
        def do_save(*_):
            try:
                value = safe_float(field.text)
                if value < 0: raise ValueError("Selling price cannot be negative.")
                product["sell"] = value
                self.manager.app.db.save()
                popup.dismiss()
                self.on_pre_enter()
            except Exception as e:
                status.text = str(e)
        save.bind(on_release=do_save)
        popup.open()

    def show_receipt(self, sale):

        snap = sale_snapshot(sale)

        when = parse_record_datetime(
            sale.get("date")
        )

        date_text = (
            when.strftime("%Y-%m-%d %H:%M")
            if when
            else str(sale.get("date", ""))
        )

        receipt = (

            f"{self.shop_name()}\n"
            f"SHOP RECEIPT\n"
            f"{'-' * 32}\n"
            f"Date: {date_text}\n"
            f"Item: {sale.get('product', '')}\n"
            f"Qty: {snap['qty']:g} "
            f"{sale.get('unit', 'Piece')}\n"
            f"Selling price: "
            f"{money(snap['selling_price'])}\n"
            f"TOTAL: "
            f"{money(snap['total'])}\n"
            f"Profit: "
            f"{money(snap['gross_profit'])}\n"
            f"{'-' * 32}\n"
            f"Thank you."
        )

        self.show_text_popup(receipt, "Receipt")

    def copy_text(self, text):

        try:

            from kivy.core.clipboard import Clipboard

            Clipboard.copy(text)

            self.msg(
                "Receipt copied."
            )

        except Exception as e:

            self.msg(str(e))


class Categories(Products):
    """Product Shelves: the same phone-style folder manager as Products."""
    SCREEN_TITLE = "Product Shelves"


class Sale(Base):
    """Cashier panel: product search + multi-item checkout + routine expense entry."""

    MAX_RESULTS = 50

    def on_pre_enter(self, *_):
        self.clear_widgets()
        db = self.manager.app.db
        layout = BoxLayout(orientation="vertical", padding=dp(8), spacing=dp(5))
        layout.add_widget(self.top("Cashier"))

        self.cart = []
        self.selected_product = None
        self.customer = AppTextInput(hint_text="Customer name (optional)", multiline=False, size_hint_y=None, height=dp(44))
        layout.add_widget(self.customer)
        self.sale_status = AppLabel(text="", size_hint_y=None, height=dp(42), font_size=sp(12))
        layout.add_widget(self.sale_status)

        if not db.products:
            layout.add_widget(AppLabel(text="No stock products yet. You can still record services and other non-stock sales above.", size_hint_y=None, height=dp(60), font_size=sp(12)))
        else:
            layout.add_widget(AppLabel(text="FIND PRODUCT", bold=True, size_hint_y=None, height=dp(26)))
            find = GridLayout(cols=2, spacing=dp(5), size_hint_y=None, height=dp(44))
            self.search = AppTextInput(hint_text="Type part of the name...", multiline=False)
            self.category_filter = AppSpinner(text="All categories", values=["All categories"] + [str(c) for c in db.categories], font_size=sp(12))
            find.add_widget(self.search)
            find.add_widget(self.category_filter)
            layout.add_widget(find)

            # Scrollable product list. It is wrapped in a fixed-height frame so the
            # page scroll and this list scroll do not get mixed up.
            self.results_box = BoxLayout(orientation="vertical", size_hint_y=None, spacing=dp(3))
            self.results_box.bind(minimum_height=self.results_box.setter("height"))
            results_scroll = SmoothScroll(do_scroll_x=False, bar_width=dp(5))
            results_scroll.add_widget(self.results_box)
            frame = BoxLayout(size_hint_y=None, height=dp(240))
            frame.add_widget(results_scroll)
            layout.add_widget(frame)

            self.selected_label = AppLabel(text="No product selected. Tap a product above.", size_hint_y=None, height=dp(42), font_size=sp(12), halign="center")
            self.selected_label.bind(width=lambda inst, w: setattr(inst, "text_size", (w, None)))
            layout.add_widget(self.selected_label)

            row = GridLayout(cols=2, spacing=dp(5), size_hint_y=None, height=dp(44))
            self.qty = AppTextInput(hint_text="Quantity", multiline=False, input_filter="float")
            add = AppButton(text="ADD TO CART")
            add.bind(on_release=self.add_to_cart)
            row.add_widget(self.qty)
            row.add_widget(add)
            layout.add_widget(row)

            self.cart_view = AppTextInput(readonly=True, multiline=True, font_size=sp(12), size_hint_y=None, height=dp(125), **mono_kwargs())
            self.autosize_text(self.cart_view, dp(125))
            layout.add_widget(self.cart_view)

            cart_buttons = GridLayout(cols=2, spacing=dp(5), size_hint_y=None, height=dp(40))
            remove = AppButton(text="REMOVE LAST ITEM", font_size=sp(12))
            clear = AppButton(text="CLEAR CART", font_size=sp(12))
            remove.bind(on_release=self.remove_last)
            clear.bind(on_release=self.clear_cart)
            cart_buttons.add_widget(remove)
            cart_buttons.add_widget(clear)
            layout.add_widget(cart_buttons)

            payrow = GridLayout(cols=2, spacing=dp(5), size_hint_y=None, height=dp(44))
            self.cash = AppTextInput(hint_text="Cash received", multiline=False, input_filter="float")
            checkout = AppButton(text="COMPLETE SALE")
            checkout.bind(on_release=self.complete_sale)
            payrow.add_widget(self.cash); payrow.add_widget(checkout); layout.add_widget(payrow)
            self.search.bind(text=lambda *_: self.refresh_results())
            self.category_filter.bind(text=lambda *_: self.refresh_results())

        layout.add_widget(AppLabel(text="ROUTINE EXPENSE", bold=True, size_hint_y=None, height=dp(28)))
        exp_actions = GridLayout(cols=2, spacing=dp(5), size_hint_y=None, height=dp(46))
        exp_save = AppButton(text="RECORD EXPENSE", size_hint_y=None, height=dp(44))
        exp_save.bind(on_release=self.open_cashier_expense)
        other_income = AppButton(text="RECORD A SERVICE", size_hint_y=None, height=dp(44),
                                 background_color=SUCCESS, font_size=sp(12))
        other_income.bind(on_release=self.open_nonstock_sale)
        exp_actions.add_widget(exp_save)
        exp_actions.add_widget(other_income)
        layout.add_widget(exp_actions)
        transfer_stock = AppButton(text="TRANSFER STOCK TO SERVICES", size_hint_y=None, height=dp(44), background_color=INFO, font_size=sp(12))
        transfer_stock.bind(on_release=self.open_stock_transfer)
        layout.add_widget(transfer_stock)
        self.exp_status = AppLabel(text="", size_hint_y=None, height=dp(38), font_size=sp(12))
        layout.add_widget(self.exp_status)
        self.set_content(layout)
        if db.products:
            self.refresh_results()

    def open_stock_transfer(self, *_):
        """Move sale inventory into the service-stock pool; this is not a sale."""
        db = self.manager.app.db
        available = [p for p in db.products if safe_float(p.get("qty")) > 0]
        if not available:
            self.sale_status.text = "No stock is available to transfer."
            return
        panel = BoxLayout(orientation="vertical", padding=dp(10), spacing=dp(7), size_hint_y=None)
        panel.bind(minimum_height=panel.setter("height"))
        panel.add_widget(AppLabel(text="Move stock from sale stock to service stock. This does not create income.", size_hint_y=None, height=dp(48), font_size=sp(12)))
        choices = [f"{x.get('name','Item')}  (available: {safe_float(x.get('qty')):g} {x.get('unit','Piece')})" for x in available]
        chooser = AppSpinner(text=choices[0], values=choices, size_hint_y=None, height=dp(46), font_size=sp(12))
        quantity = AppTextInput(hint_text="Quantity to transfer", multiline=False, input_filter="float", size_hint_y=None, height=dp(46))
        preview = AppLabel(text="", size_hint_y=None, height=dp(42), font_size=sp(12))
        status = AppLabel(text="", size_hint_y=None, height=dp(42), font_size=sp(12))
        panel.add_widget(chooser); panel.add_widget(quantity); panel.add_widget(preview); panel.add_widget(status)
        transfer = AppButton(text="TRANSFER STOCK", size_hint_y=None, height=dp(46), background_color=INFO)
        close = AppButton(text="CLOSE", size_hint_y=None, height=dp(42), background_color=GREY)
        panel.add_widget(transfer); panel.add_widget(close)
        popup = Popup(title="Transfer Stock to Services", content=panel, size_hint=(.92, .68), auto_dismiss=False)
        def selected():
            idx = choices.index(chooser.text) if chooser.text in choices else 0
            return available[idx]
        def update_preview(*_):
            product = selected()
            q = safe_float(quantity.text or 0)
            preview.text = "Transfer value: " + money(q * safe_float(product.get("buy"))) if q > 0 else "Enter the quantity to see its stock cost."
        chooser.bind(text=update_preview); quantity.bind(text=update_preview)
        def save_transfer(*_):
            try:
                product = selected(); q = safe_float(quantity.text or 0)
                current = next((x for x in db.products if x is product), product)
                available_qty = safe_float(current.get("qty"))
                if q <= 0: raise ValueError("Enter a quantity greater than zero.")
                if q > available_qty + 1e-9: raise ValueError(f"Only {available_qty:g} is available for sale.")
                unit_cost = max(0.0, safe_float(current.get("buy")))
                value = q * unit_cost
                current["qty"] = round(available_qty - q, 6)
                transfers = db.settings.setdefault("service_stock_transfers", [])
                transfers.append({"date": datetime.now().isoformat(), "product": str(current.get("name", "Item")),
                                  "product_pid": str(current.get("pid", "")), "qty": q,
                                  "unit": str(current.get("unit", "Piece")), "unit_cost": unit_cost,
                                  "original_cost": value, "remaining_cost": value, "allocated_cost": 0.0})
                db.save()
                popup.dismiss()
                self.sale_status.text = f"STOCK TRANSFERRED: {current.get('name','Item')} — {money(value)} moved to service stock. No income, no loss. Service income will first cover this cost, then show as profit."
                self.refresh_results()
            except Exception as e:
                status.text = "ERROR: " + str(e)
        transfer.bind(on_release=save_transfer); close.bind(on_release=lambda *_: popup.dismiss())
        popup.open()

    def open_nonstock_sale(self, *_):
        """Record service income with only a service name and amount."""
        panel = BoxLayout(orientation="vertical", padding=dp(10), spacing=dp(8), size_hint_y=None)
        panel.bind(minimum_height=panel.setter("height"))
        panel.add_widget(AppLabel(
            text="Enter the service name and the money received. The system handles transferred stock cost automatically.",
            size_hint_y=None, height=dp(58), font_size=sp(12)))
        service = AppTextInput(hint_text="Service name (e.g. Photocopying)", multiline=False,
                               size_hint_y=None, height=dp(48))
        amount = AppTextInput(hint_text="Amount received", multiline=False, input_filter="float",
                              size_hint_y=None, height=dp(48))
        status = AppLabel(text="", size_hint_y=None, height=dp(42), font_size=sp(12))
        panel.add_widget(service)
        panel.add_widget(amount)
        panel.add_widget(status)
        save = AppButton(text="RECORD SERVICE", size_hint_y=None, height=dp(48), background_color=SUCCESS)
        close = AppButton(text="CLOSE", size_hint_y=None, height=dp(42), background_color=GREY)
        panel.add_widget(save)
        panel.add_widget(close)
        popup = Popup(title="Record a Service", content=panel, size_hint=(.92, .58), auto_dismiss=False)

        def save_record(*_):
            try:
                name = service.text.strip()
                total = safe_float(amount.text or 0)
                if not name:
                    raise ValueError("Enter the service name.")
                if total <= 0:
                    raise ValueError("Enter an amount greater than zero.")

                db = self.manager.app.db
                # Service income is allocated against the oldest transferred service
                # stock cost. The cashier does not have to count sheets or enter costs.
                transfers = db.settings.setdefault("service_stock_transfers", [])
                available_service_cost = sum(
                    max(0.0, safe_float(t.get("remaining_cost"))) for t in transfers)
                allocated_cost = min(total, available_service_cost)
                left_to_allocate = allocated_cost
                for transfer_row in transfers:
                    remaining_cost = max(0.0, safe_float(transfer_row.get("remaining_cost")))
                    take = min(remaining_cost, left_to_allocate)
                    if take > 0:
                        transfer_row["remaining_cost"] = round(remaining_cost - take, 2)
                        transfer_row["allocated_cost"] = round(
                            safe_float(transfer_row.get("allocated_cost")) + take, 2)
                        left_to_allocate -= take
                    if left_to_allocate <= 0.004:
                        break

                timestamp = datetime.now().isoformat()
                base_no = datetime.now().strftime("%Y%m%d%H%M%S")
                used = {str(x.get("receipt_no")) for x in db.sales[-300:]}
                receipt_no = base_no
                n = 2
                while receipt_no in used:
                    receipt_no = f"{base_no}-{n}"
                    n += 1
                record = {
                    "date": timestamp, "product": name, "unit": "Service", "qty": 1,
                    "selling_price": total, "sell_price": total,
                    "unit_cost": allocated_cost, "cost": allocated_cost,
                    "total": total, "gross_profit": total - allocated_cost,
                    "profit": total - allocated_cost, "unit_profit": total - allocated_cost,
                    "receipt_no": receipt_no, "customer_name": "",
                    "cash_paid": total, "change_given": 0,
                    "amount_paid": total, "credit_amount": 0,
                    "method": "cash", "sale_type": "non_stock",
                    "income_category": "Service",
                    "service_stock_cost_allocated": allocated_cost
                }
                db.sales.append(record)
                db.save()
                receipt = self.build_receipt([record], total, 0, receipt_no)
                popup.dismiss()
                self.sale_status.text = (
                    f"SERVICE RECORDED: {name} — {money(total)}. "
                    f"Used to cover transferred stock cost: {money(allocated_cost)}. "
                    f"Service profit now: {money(total - allocated_cost)}. "
                    + (f"Stock cost still to cover: {money(sum(max(0.0, safe_float(t.get('remaining_cost'))) for t in transfers))} (not a loss)."
                       if any(safe_float(t.get('remaining_cost')) > 0.004 for t in transfers) else "Stock cost fully covered."))
                self.show_text_popup(receipt, "Service Receipt")
            except Exception as e:
                status.text = "ERROR: " + str(e)

        save.bind(on_release=save_record)
        close.bind(on_release=lambda *_: popup.dismiss())
        popup.open()

    def refresh_results(self):
        """Filter the product list by the words typed and by category."""
        db = self.manager.app.db
        self.results_box.clear_widgets()
        words = self.search.text.strip().lower().split()
        category = self.category_filter.text
        matches = []
        for p in db.products:
            if category != "All categories" and str(p.get("category", "")) != category:
                continue
            haystack = (str(p.get("name", "")) + " " + str(p.get("category", ""))).lower()
            if all(w in haystack for w in words):
                matches.append(p)
        matches.sort(key=lambda p: str(p.get("name", "")).lower())

        if not matches:
            self.results_box.add_widget(AppLabel(text="No product matches. Try fewer letters.", size_hint_y=None, height=dp(44)))
            return
        for p in matches[:self.MAX_RESULTS]:
            name = str(p.get("name", ""))
            stock = safe_float(p.get("qty", 0))
            unit = p.get("unit", "Piece")
            if stock > 0:
                text = f"{name}\nStock: {stock:g} {unit}   •   {money(p.get('sell', 0))}"
            else:
                text = f"{name}\nOUT OF STOCK"
            b = AppButton(text=text, size_hint_y=None, height=dp(54), font_size=sp(13), disabled=stock <= 0)
            b.bind(on_release=lambda _, p=p: self.select_product(p))
            self.results_box.add_widget(b)
        if len(matches) > self.MAX_RESULTS:
            self.results_box.add_widget(AppLabel(
                text=f"Showing the first {self.MAX_RESULTS} of {len(matches)}. Type more letters to narrow the list.",
                size_hint_y=None, height=dp(36), font_size=sp(11)))

    def select_product(self, product):
        self.selected_product = product
        unit = product.get("unit", "Piece")
        self.selected_label.text = (f"SELECTED: {product.get('name', '')}\n"
                                    f"{money(product.get('sell', 0))} per {unit}  •  in stock: {safe_float(product.get('qty', 0)):g}")
        self.qty.text = "1"
        self.sale_status.text = ""

    def add_to_cart(self, *_):
        try:
            product = self.selected_product
            if product is None: raise ValueError("Tap a product in the list first.")
            qty = float(self.qty.text or 0)
            if qty <= 0: raise ValueError("Quantity must be greater than zero.")
            available = safe_float(product.get("qty", 0))
            already = sum(x["qty"] for x in self.cart if x["product"] is product)
            if qty + already > available: raise ValueError(f"Available stock: {available:g} {product.get('unit','Piece')}")
            price = safe_float(product.get("sell", 0))
            self.cart.append({"product": product, "qty": qty, "price": price})
            self.qty.text = ""
            self.selected_product = None
            self.selected_label.text = "No product selected. Tap a product above."
            self.sale_status.text = f"Added: {product.get('name', '')}"
            self.refresh_cart()
        except Exception as e:
            self.sale_status.text = "ERROR: " + str(e)

    def remove_last(self, *_):
        if self.cart:
            self.cart.pop()
            self.refresh_cart()

    def clear_cart(self, *_):
        self.cart = []
        self.refresh_cart()

    def refresh_cart(self):
        wd, al = [16, 4, 8, 9], ["l", "r", "r", "r"]
        rule = "-" * RECEIPT_WIDTH
        lines = fmt_row(["ITEM", "QTY", "PRICE", "TOTAL"], wd, al) + [rule]
        total = 0.0
        for x in self.cart:
            sub = x["qty"] * x["price"]; total += sub
            lines += fmt_row([cap(x["product"].get("name", "")), f"{x['qty']:g}", num(x["price"]), num(sub)], wd, al, wrap=0)
        lines += [rule, _lr("TOTAL", num(total), RECEIPT_WIDTH)]
        self.cart_view.text = "\n".join(lines)

    def complete_sale(self, *_):
        try:
            if not self.cart: raise ValueError("Cart is empty.")
            total = sum(x["qty"] * x["price"] for x in self.cart)
            cash = safe_float(self.cash.text or 0)
            if cash < 0: raise ValueError("Cash received cannot be negative.")
            credit_total = max(0.0, total - cash)
            if credit_total > 0.004 and not self.customer.text.strip():
                raise ValueError(f"Cash is short by {money(credit_total)}. Enter the customer's name to record the balance as a credit sale.")
            db = self.manager.app.db
            # Cloud sync can swap a product record for a newer copy while the cart is open. Re-resolve every
            # cart line to the live record so stock is deducted from the right object, and re-check stock.
            need = {}
            for x in self.cart:
                p = x["product"]; pid = str(p.get("pid", "") or "")
                live = next((q for q in db.products if pid and str(q.get("pid", "")) == pid), None)
                x["product"] = live if live is not None else p
                key = id(x["product"]); need[key] = need.get(key, 0.0) + x["qty"]
                if need[key] > safe_float(x["product"].get("qty", 0)) + 1e-9:
                    raise ValueError(f"Not enough stock for {x['product'].get('name','')}: available {safe_float(x['product'].get('qty',0)):g}")
            tag = hashlib.sha1(device_id().encode()).hexdigest()[:2] if _sync_license_info() else ""
            # Cost, profit, tax, paid/credit split and the receipt number are all captured by the engine.
            saved_sales = capture_sale(db, self.cart, cash, self.customer.text.strip(), device_tag=tag)
            receipt_no = saved_sales[0]["receipt_no"]
            total = sum(s["total"] for s in saved_sales)
            db.save()
            receipt=self.build_receipt(saved_sales, cash, max(0.0,cash-total), receipt_no)
            self.cart=[]; self.cash.text=""; self.refresh_cart(); self.customer.text=""
            self.selected_product=None
            self.selected_label.text="No product selected. Tap a product above."
            self.refresh_results()
            self.sale_status.text="SALE SAVED. Receipt can be reprinted later from PAST RECEIPTS."
            self.show_text_popup(receipt, "Receipt")
        except Exception as e:
            self.sale_status.text="ERROR: " + str(e)

    def build_receipt(self, sales, cash, change, receipt_no):
        return receipt_text(self.shop_name(), sales, receipt_no, cash, change)

    def open_cashier_expense(self, *_):
        """Open the original expense details and amount fields in a popup."""
        panel = BoxLayout(orientation="vertical", padding=dp(10), spacing=dp(7), size_hint_y=None)
        panel.bind(minimum_height=panel.setter("height"))
        panel.add_widget(AppLabel(text="Enter the expense details and amount.",
                                  size_hint_y=None, height=dp(42), font_size=sp(12)))
        self.exp_desc = AppTextInput(hint_text="Expense e.g. Employees lunch", multiline=False,
                                     size_hint_y=None, height=dp(46))
        self.exp_amount = AppTextInput(hint_text="Amount", multiline=False, input_filter="float",
                                       size_hint_y=None, height=dp(46))
        self.exp_status = AppLabel(text="", size_hint_y=None, height=dp(42), font_size=sp(12))
        record = AppButton(text="RECORD EXPENSE", size_hint_y=None, height=dp(46))
        close = AppButton(text="CLOSE", size_hint_y=None, height=dp(42), background_color=GREY)
        for widget in (self.exp_desc, self.exp_amount, self.exp_status, record, close):
            panel.add_widget(widget)
        popup = Popup(title="Record Expense", content=panel, size_hint=(.90, .48), auto_dismiss=False)

        def record_expense(*_):
            self.save_cashier_expense()
            if self.exp_status.text.startswith("EXPENSE SAVED:"):
                popup.dismiss()

        record.bind(on_release=record_expense)
        close.bind(on_release=lambda *_: popup.dismiss())
        popup.open()

    def save_cashier_expense(self, *_):
        try:
            description=self.exp_desc.text.strip(); amount=safe_float(self.exp_amount.text or 0)
            if not description: raise ValueError("Expense description is required.")
            if amount <= 0: raise ValueError("Expense amount must be greater than zero.")
            db=self.manager.app.db
            capture_expense(db, description, amount)["entered_from"]="cashier"
            db.save(); self.exp_desc.text=""; self.exp_amount.text=""; self.exp_status.text=f"EXPENSE SAVED: {description} — {money(amount)}"
        except Exception as e:self.exp_status.text="ERROR: "+str(e)


class Reports(Base):

    def __init__(self, **kwargs):

        super().__init__(**kwargs)

        self.kind = "daily"
        self.statement_text = ""
        self.period_starts = []
        self.period_labels = []
        self.period_spinner = None
        self.current_start = None

    def on_pre_enter(self, *_):

        self.clear_widgets()

        db = self.manager.app.db

        try:
            db.settle_periods()   # settle any week / month that ended since last time
        except Exception:
            pass

        layout = BoxLayout(
            orientation="vertical",
            padding=dp(8),
            spacing=dp(5)
        )

        layout.add_widget(self.top("Reports / Statements"))

        tabs = GridLayout(cols=3, spacing=dp(4), size_hint_y=None, height=dp(44))
        self.tab_buttons = {}
        for kind, text in (("daily", "DAILY"), ("weekly", "WEEKLY"), ("monthly", "MONTHLY")):
            button = AppButton(text=text)
            button.bind(on_release=lambda _, k=kind: self.select_kind(k))
            self.tab_buttons[kind] = button
            tabs.add_widget(button)
        layout.add_widget(tabs)

        self.picker = BoxLayout(orientation="vertical", spacing=dp(4), size_hint_y=None, height=dp(46))
        self.picker.bind(minimum_height=self.picker.setter("height"))
        layout.add_widget(self.picker)

        self.hint = AppLabel(text="", font_size=sp(11), size_hint_y=None, height=dp(54), halign="center")
        self.hint.bind(width=lambda inst, w: setattr(inst, "text_size", (w, None)))
        layout.add_widget(self.hint)

        controls = GridLayout(cols=2, spacing=dp(5), size_hint_y=None, height=dp(45))
        show = AppButton(text="SHOW / REFRESH")
        export = AppButton(text="EXPORT / PRINT")
        show.bind(on_release=self.show_statement)
        export.bind(on_release=self.export_statement)
        controls.add_widget(show)
        controls.add_widget(export)
        layout.add_widget(controls)

        self.statement_view = AppTextInput(readonly=True, multiline=True, font_size=sp(11), use_bubble=False, use_handles=False, **mono_kwargs())
        self.autosize_text(self.statement_view, dp(320))
        layout.add_widget(self.statement_view)

        self.set_content(layout)

        self.select_kind("daily")

    # ------------------------------------------------------------ pickers
    def select_kind(self, kind):

        self.kind = kind

        # Keep every period tab readable: inactive tabs use a pale blue fill
        # and dark text instead of white-on-white; the selected tab is solid blue.
        for k, button in self.tab_buttons.items():
            if k == kind:
                button.background_color = PRIMARY
                button.color = (1, 1, 1, 1)
            else:
                button.background_color = SELECT_BG
                button.color = PRIMARY

        self.picker.clear_widgets()
        self.period_spinner = None

        if kind == "daily":
            self.build_daily_picker()
        else:
            self.build_period_picker(kind)

        self.show_statement()

    def build_daily_picker(self):

        row = BoxLayout(orientation="horizontal", spacing=dp(4), size_hint_y=None, height=dp(46))
        prev = AppButton(text="‹ DAY", size_hint_x=None, width=dp(78), font_size=sp(12))
        nxt = AppButton(text="DAY ›", size_hint_x=None, width=dp(78), font_size=sp(12))
        self.date_input = AppTextInput(text=today_date().isoformat(), multiline=False)
        prev.bind(on_release=lambda *_: self.shift_day(-1))
        nxt.bind(on_release=lambda *_: self.shift_day(1))
        self.date_input.bind(on_text_validate=lambda *_: self.show_statement())
        row.add_widget(prev)
        row.add_widget(self.date_input)
        row.add_widget(nxt)
        self.picker.add_widget(row)
        self.hint.text = ("Daily statement. Today is still open. Use ‹ DAY / DAY › or type a date "
                          "(YYYY-MM-DD). Daily figures are not stored separately; they are "
                          "included in their week's statement.")

    def shift_day(self, delta):

        try:
            d = datetime.strptime(self.date_input.text.strip(), "%Y-%m-%d").date()
        except Exception:
            d = today_date()

        self.date_input.text = (d + timedelta(days=delta)).isoformat()
        self.show_statement()

    def build_period_picker(self, kind):

        db = self.manager.app.db

        if kind == "weekly":
            self.period_starts = completed_weeks(db)
            self.period_labels = [week_label(s) for s in self.period_starts]
            self.hint.text = ("Completed weeks only (Monday to Sunday), newest first. The week still "
                              "running is not shown. Use ‹ OLDER / NEWER › or tap the box to pick a week.")
            empty = "No completed week yet. A week is settled automatically when it ends (Sunday night)."
        else:
            self.period_starts = completed_months(db)
            self.period_labels = [month_label(s) for s in self.period_starts]
            self.hint.text = ("Completed months only, newest first. The month still running is not "
                              "shown. Use ‹ OLDER / NEWER › or tap the box to pick a month.")
            empty = "No completed month yet. A month is settled automatically when it ends."

        if not self.period_starts:
            self.picker.add_widget(AppLabel(text=empty, size_hint_y=None, height=dp(60), font_size=sp(12)))
            return

        row = BoxLayout(orientation="horizontal", spacing=dp(4), size_hint_y=None, height=dp(46))
        older = AppButton(text="‹ OLDER", size_hint_x=None, width=dp(78), font_size=sp(12))
        newer = AppButton(text="NEWER ›", size_hint_x=None, width=dp(78), font_size=sp(12))
        self.period_spinner = AppSpinner(text=self.period_labels[0], values=self.period_labels, font_size=sp(13))
        self.period_spinner.bind(text=lambda *_: self.show_statement())
        older.bind(on_release=lambda *_: self.step_period(1))
        newer.bind(on_release=lambda *_: self.step_period(-1))
        row.add_widget(older)
        row.add_widget(self.period_spinner)
        row.add_widget(newer)
        self.picker.add_widget(row)

    def step_period(self, delta):

        if not self.period_spinner:
            return

        try:
            index = self.period_labels.index(self.period_spinner.text)
        except ValueError:
            index = 0

        index += delta

        if 0 <= index < len(self.period_labels):
            self.period_spinner.text = self.period_labels[index]

    # ------------------------------------------------------------ statement
    def show_statement(self, *_):

        try:

            db = self.manager.app.db
            settled = None

            if self.kind == "daily":

                try:
                    start, end = period_bounds("daily", self.date_input.text.strip())
                except ValueError:
                    raise ValueError("Enter the date as YYYY-MM-DD, for example " + today_date().isoformat())

            else:

                if not self.period_starts or not self.period_spinner:
                    self.current_start = None
                    self.statement_text = (
                        "Nothing to show yet.\n\n"
                        "Weekly and monthly statements appear here after the week or month has ended. "
                        "They are settled and saved automatically."
                    )
                    self.statement_view.text = self.statement_text
                    return

                index = self.period_labels.index(self.period_spinner.text)
                chosen = self.period_starts[index]

                if self.kind == "weekly":
                    key = chosen.isoformat()
                    start, end = period_bounds("weekly", key)
                    settled = db.weekly_settlements.get(key)
                else:
                    key = chosen.strftime("%Y-%m")
                    start, end = period_bounds("monthly", key)
                    settled = db.monthly_settlements.get(key)

            self.current_start = start

            sales, expenses = get_period_records(db, start, end)
            purchases = get_period_purchases(db, start, end)
            last_day = end - timedelta(days=1)
            capital_start = capital_as_of(db, start - timedelta(days=1))
            capital_end = capital_as_of(db, last_day)

            self.statement_text = build_statement_text(
                self.manager.app.confirmed_shop_name(),
                self.kind,
                start,
                end,
                sales,
                expenses,
                purchases,
                capital_start,
                capital_end,
                (settled or {}).get("settled_at"),
                (settled or {}).get("capital_inventory", sum(max(0.0, safe_float(p.get("qty", 0))) * max(0.0, safe_float(p.get("buy", 0))) for p in db.products)),
                (settled or {}).get("capital_cash", capital_end - sum(max(0.0, safe_float(p.get("qty", 0))) * max(0.0, safe_float(p.get("buy", 0))) for p in db.products)),
                fin=fin_compute(db, start, end),
                shop_db=db
            )

            self.statement_view.text = self.statement_text

        except Exception as e:

            self.statement_text = "STATEMENT ERROR\n\n" + str(e)
            self.statement_view.text = self.statement_text

    def export_statement(self, *_):

        try:

            self.show_statement()

            if not self.current_start:
                raise ValueError("There is no statement to export yet.")

            base = os.path.dirname(data_path("settings.json"))
            folder = os.path.join(base, "statements")
            os.makedirs(folder, exist_ok=True)

            if self.kind == "monthly":
                name = "monthly_statement_" + self.current_start.strftime("%Y-%m") + ".txt"
            else:
                name = f"{self.kind}_statement_" + self.current_start.isoformat() + ".txt"

            path = os.path.join(folder, name)

            with open(path, "w", encoding="utf-8") as file:
                file.write(self.statement_text)

            # A copy is kept in the app folder; the popup lets the user save to the
            # phone's storage, print, share or copy the statement.
            self.show_text_popup(self.statement_text, "Statement", filename=name)

        except Exception as e:

            self.msg("Could not export statement:\n" + str(e))


class Receipts(Base):
    """Find any past order and print / share / copy its receipt again."""

    MAX_RESULTS = 40

    def on_pre_enter(self, *_):
        self.clear_widgets()
        layout = BoxLayout(orientation="vertical", padding=dp(8), spacing=dp(5))
        layout.add_widget(self.top("Receipts / Reprint"))

        self.search = AppTextInput(hint_text="Search ALL dates: receipt no., customer or product", multiline=False, size_hint_y=None, height=dp(44))
        layout.add_widget(self.search)

        row = BoxLayout(orientation="horizontal", spacing=dp(4), size_hint_y=None, height=dp(44))
        prev = AppButton(text="‹ DAY", size_hint_x=None, width=dp(72), font_size=sp(12))
        nxt = AppButton(text="DAY ›", size_hint_x=None, width=dp(72), font_size=sp(12))
        self.day = AppTextInput(text=today_date().isoformat(), multiline=False)
        prev.bind(on_release=lambda *_: self.shift_day(-1))
        nxt.bind(on_release=lambda *_: self.shift_day(1))
        row.add_widget(prev); row.add_widget(self.day); row.add_widget(nxt)
        layout.add_widget(row)

        self.info = AppLabel(text="", font_size=sp(12), size_hint_y=None, height=dp(44), halign="center")
        self.info.bind(width=lambda inst, w: setattr(inst, "text_size", (w, None)))
        layout.add_widget(self.info)

        self.list_box = BoxLayout(orientation="vertical", size_hint_y=None, spacing=dp(4))
        self.list_box.bind(minimum_height=self.list_box.setter("height"))
        layout.add_widget(self.list_box)

        self.search.bind(text=lambda *_: self.refresh())
        self.day.bind(on_text_validate=lambda *_: self.refresh())
        self.set_content(layout)
        self.refresh()

    def shift_day(self, delta):
        try:
            d = datetime.strptime(self.day.text.strip(), "%Y-%m-%d").date()
        except Exception:
            d = today_date()
        self.day.text = (d + timedelta(days=delta)).isoformat()
        self.refresh()

    def refresh(self, *_):
        db = self.manager.app.db
        self.list_box.clear_widgets()
        query = self.search.text.strip().lower()
        orders = group_orders(db.sales)
        if query:
            found = [o for o in orders
                     if query in o["receipt_no"].lower() or query in o["customer"].lower()
                     or any(query in it["name"].lower() for it in o["items"])]
            heading = "Search results (all dates)"
        else:
            try:
                day = datetime.strptime(self.day.text.strip(), "%Y-%m-%d").date()
            except Exception:
                self.info.text = "Enter the date as YYYY-MM-DD, for example " + today_date().isoformat()
                return
            found = [o for o in orders if o["when"] and o["when"].date() == day]
            heading = "Orders on " + fmt_day(day)
        found.reverse()  # newest first
        self.info.text = f"{heading}: {len(found)} order(s). Tap one to print / share."
        if not found:
            self.list_box.add_widget(AppLabel(text="No receipts found.", size_hint_y=None, height=dp(40)))
            return
        for order in found[:self.MAX_RESULTS]:
            when = order["when"]
            stamp = when.strftime("%d %b %Y %H:%M") if when else "no date"
            number = f"#{order['receipt_no']}" if order["receipt_no"] else "no receipt no."
            who = order["customer"] or "Walk-in"
            text = f"{stamp}   •   {number}\n{who}   •   {len(order['items'])} item(s)   •   Total {money(order['total'])}"
            b = AppButton(text=text, size_hint_y=None, height=dp(58), font_size=sp(12))
            b.bind(on_release=lambda _, o=order: self.open_receipt(o))
            self.list_box.add_widget(b)
        if len(found) > self.MAX_RESULTS:
            self.list_box.add_widget(AppLabel(text=f"Showing the newest {self.MAX_RESULTS} of {len(found)}. Use search or change the day to narrow down.", size_hint_y=None, height=dp(40), font_size=sp(11)))

    def open_receipt(self, order):
        text = receipt_text(self.shop_name(), order["lines"], order["receipt_no"] or "-", reprint=True)
        self.show_text_popup(text, "Receipt")


class Expenses(Base):

    def on_pre_enter(self, *_):

        self.clear_widgets()

        layout = BoxLayout(
            orientation="vertical",
            padding=dp(10),
            spacing=dp(7)
        )

        layout.add_widget(
            self.top("Expenses")
        )

        description = AppTextInput(
            hint_text="Expense description",
            multiline=False,
            size_hint_y=None,
            height=dp(46)
        )

        amount = AppTextInput(
            hint_text="Amount",
            input_filter="float",
            multiline=False,
            size_hint_y=None,
            height=dp(46)
        )

        save = AppButton(
            text="SAVE EXPENSE",
            size_hint_y=None,
            height=dp(48)
        )

        status = AppLabel(
            text="",
            size_hint_y=None,
            height=dp(45)
        )

        layout.add_widget(description)
        layout.add_widget(amount)
        layout.add_widget(save)
        layout.add_widget(status)

        save.bind(
            on_release=lambda *_:
            self.save_expense(
                description,
                amount,
                status
            )
        )

        layout.add_widget(
            AppLabel(
                text="Today's expenses",
                bold=True,
                size_hint_y=None,
                height=dp(30)
            )
        )

        scroll = SmoothScroll()

        box = BoxLayout(
            orientation="vertical",
            size_hint_y=None,
            spacing=dp(3)
        )

        box.bind(
            minimum_height=box.setter("height")
        )

        today = today_date()

        tomorrow = (
            today +
            __import__("datetime").timedelta(
                days=1
            )
        )

        for expense in reversed(
            self.manager.app.db.expenses
        ):

            d = record_date(
                expense.get("date")
            )

            if d and today <= d < tomorrow:

                box.add_widget(
                    AppLabel(
                        text=(
                            f"{time_text(expense.get('date'))}  "
                            f"{expense.get('description', '')}"
                            f"  —  "
                            f"{money(expense.get('amount', 0))}"
                        ),
                        size_hint_y=None,
                        height=dp(38),
                        font_size=sp(13)
                    )
                )

        scroll.add_widget(box)

        layout.add_widget(scroll)

        self.set_content(layout)

    def save_expense(
        self,
        description,
        amount,
        status
    ):

        try:

            name = description.text.strip()

            value = float(
                amount.text or 0
            )

            if not name:

                raise ValueError(
                    "Expense description is required."
                )

            if value <= 0:

                raise ValueError(
                    "Expense amount must be greater than zero."
                )

            capture_expense(self.manager.app.db, name, value)   # category is derived automatically

            self.manager.app.db.save()

            description.text = ""
            amount.text = ""

            status.text = (
                "Expense saved."
            )

            self.on_pre_enter()

        except Exception as e:

            status.text = str(e)


class Settings(Base):

    def on_pre_enter(self, *_):

        self.clear_widgets()

        layout = BoxLayout(
            orientation="vertical",
            padding=dp(10),
            spacing=dp(8)
        )

        layout.add_widget(
            self.top("Settings")
        )

        shop_name = (
            self.manager.app
            .confirmed_shop_name()
        )

        layout.add_widget(
            AppLabel(
                text=(
                    "SHOP NAME "
                    "(DEVELOPER CONFIRMED)"
                ),
                bold=True,
                size_hint_y=None,
                height=dp(32)
            )
        )

        name_field = AppTextInput(
            text=shop_name,
            readonly=True,
            multiline=False,
            size_hint_y=None,
            height=dp(48)
        )

        layout.add_widget(
            name_field
        )

        layout.add_widget(
            AppLabel(
                text=(
                    "This shop name comes from "
                    "the signed developer license.\n"
                    "It cannot be changed from Settings."
                ),
                font_size=sp(12),
                size_hint_y=None,
                height=dp(55)
            )
        )

        layout.add_widget(
            AppLabel(
                text=f"App version: {APP_VERSION}",
                size_hint_y=None,
                height=dp(35)
            )
        )

        layout.add_widget(
            AppLabel(
                text=(
                    "Daily settlement is automatic "
                    "by calendar date.\n"
                    "Previous sales remain recorded."
                ),
                font_size=sp(12),
                size_hint_y=None,
                height=dp(55)
            )
        )

        self.set_content(layout)
        
class License(Base):
    """First-run onboarding: request a new business or join an existing business."""
    def on_pre_enter(self, *_):
        self.clear_widgets()
        outer = BoxLayout(orientation="vertical", padding=dp(8), spacing=dp(6))
        required = getattr(self.manager.app, "license_required", False)
        outer.add_widget(AppLabel(text="WELCOME TO SHOP MANAGEMENT" if required else "ACTIVATION / BUSINESS ACCESS",
                                  font_size=sp(21), bold=True, size_hint_y=None, height=dp(48)))
        outer.add_widget(AppLabel(text="Choose how this phone should connect to a business.",
                                  font_size=sp(13), size_hint_y=None, height=dp(38)))
        choices = GridLayout(cols=2, spacing=dp(7), size_hint_y=None, height=dp(78))
        req_btn = AppButton(text="REQUEST NEW\nBUSINESS", font_size=sp(13))
        join_btn = AppButton(text="JOIN EXISTING\nBUSINESS", font_size=sp(13))
        choices.add_widget(req_btn); choices.add_widget(join_btn); outer.add_widget(choices)

        scroll = SmoothScroll(do_scroll_x=False, bar_width=dp(4))
        self.panel = BoxLayout(orientation="vertical", padding=dp(8), spacing=dp(7), size_hint_y=None)
        self.panel.bind(minimum_height=self.panel.setter("height"))
        scroll.add_widget(self.panel); outer.add_widget(scroll); self.add_widget(outer)
        self.mode_status = AppLabel(text="Select one of the two options above.", font_size=sp(12),
                                    size_hint_y=None, height=dp(52), halign="left", valign="middle")
        self.mode_status.bind(size=lambda o,v:setattr(o,"text_size",(o.width,None)))
        outer.add_widget(self.mode_status)
        if required:
            # Locked: there is no button that leads into the shop. Only a valid licence / join code unlocks it.
            recheck = AppButton(text="CHECK LICENSE ONLINE AGAIN", size_hint_y=None, height=dp(44))
            recheck.bind(on_release=self.recheck_license)
            outer.add_widget(recheck)
        else:
            back_text = "BACK TO ADMIN DASHBOARD" if getattr(self.manager.app, "admin_session", False) else "BACK TO SHOP DASHBOARD"
            back_btn = AppButton(text=back_text, size_hint_y=None, height=dp(44))
            def leave_license(*_):
                app = self.manager.app
                self.manager.current = "admin" if getattr(app, "admin_session", False) else "home"
            back_btn.bind(on_release=leave_license)
            outer.add_widget(back_btn)
        req_btn.bind(on_release=lambda *_: self.show_mode("activation"))
        join_btn.bind(on_release=lambda *_: self.show_mode("join"))
        # Returning administrators can still open this screen to manage access.
        if not required and _cloud_registration():
            self.show_mode("devices")
        elif required and getattr(self.manager.app, "license_state", "") in ("expired", "revoked"):
            self.show_mode("activation")         # straight to "request a new licence"
        else:
            self.show_mode("welcome")

    def show_mode(self, mode):
        self.mode = mode
        self.panel.clear_widgets()
        if mode == "welcome":
            self.panel.add_widget(AppLabel(text="NEW BUSINESS: request approval from the developer.\nEXISTING BUSINESS: join with a single-use code from the owner.",
                                           font_size=sp(13), size_hint_y=None, height=dp(72), halign="left"))
            self.mode_status.text = (getattr(self.manager.app, "license_message", "") if getattr(self.manager.app, "license_required", False)
                                     else "Your business data stays on this device until a valid cloud registration is completed.")
            return
        if mode == "activation":
            self.panel.add_widget(AppLabel(text="REQUEST ACTIVATION FOR A NEW BUSINESS", bold=True, size_hint_y=None, height=dp(34)))
            default_business = getattr(self.manager.app, "license_business", "") or self.manager.app.db.settings.get("business_name", "")
            self.business_input = AppTextInput(text="" if default_business == "My Shop" else default_business,
                hint_text="Business name (required)", multiline=False, size_hint_y=None, height=dp(46))
            self.contact_input = AppTextInput(hint_text="Contact / phone number (required)", multiline=False,
                size_hint_y=None, height=dp(46))
            self.panel.add_widget(self.business_input); self.panel.add_widget(self.contact_input)
            self.panel.add_widget(AppLabel(text="Device ID: " + device_id(), font_size=sp(11),
                                           size_hint_y=None, height=dp(40), halign="left"))
            row = GridLayout(cols=2, spacing=dp(6), size_hint_y=None, height=dp(46))
            copy_req = AppButton(text="COPY DEVICE REQUEST"); copy_req.bind(on_release=lambda *_: self.copy(make_device_request(), self.mode_status))
            online = AppButton(text="SUBMIT ACTIVATION REQUEST"); online.bind(on_release=self.request_online)
            self.submit_btn = online
            row.add_widget(copy_req); row.add_widget(online); self.panel.add_widget(row)
            self._refresh_submit_btn()
            check = AppButton(text="CHECK ONLINE ACTIVATION", size_hint_y=None, height=dp(45)); check.bind(on_release=self.check_online); self.panel.add_widget(check)
            code = AppTextInput(hint_text="Optional signed activation code", multiline=True, size_hint_y=None, height=dp(86))
            self.code_box = code; self.panel.add_widget(code)
            verify = AppButton(text="ACTIVATE / VERIFY CODE", size_hint_y=None, height=dp(46)); verify.bind(on_release=lambda *_: self.activate(code, self.mode_status)); self.panel.add_widget(verify)
            support = AppButton(text="CUSTOMER SUPPORT", size_hint_y=None, height=dp(42)); support.bind(on_release=self.open_support); self.panel.add_widget(support)
            self.mode_status.text = getattr(self.manager.app, "license_message", "Ready to request activation.")
            self.refresh_support()
            if getattr(self.manager.app, "license_required", False): self.start_polling()
            return
        if mode == "join":
            self.panel.add_widget(AppLabel(text="JOIN AN ALREADY ESTABLISHED BUSINESS", bold=True, size_hint_y=None, height=dp(36)))
            self.panel.add_widget(AppLabel(text="Ask the business administrator for a fresh single-use joining code. Supabase checks the license and device limit automatically.",
                                           font_size=sp(12), size_hint_y=None, height=dp(64), halign="left"))
            self.join_code = AppTextInput(hint_text="Enter joining code", multiline=False, size_hint_y=None, height=dp(48), password=False)
            self.panel.add_widget(self.join_code)
            join = AppButton(text="JOIN BUSINESS", size_hint_y=None, height=dp(48)); join.bind(on_release=self.join_existing); self.panel.add_widget(join)
            return
        if mode == "devices":
            self.panel.add_widget(AppLabel(text="This phone is already linked to a business. Use the Admin Dashboard to manage joining codes and devices.",
                                           font_size=sp(13), size_hint_y=None, height=dp(70), halign="left"))
            go = AppButton(text="OPEN SHOP DASHBOARD", size_hint_y=None, height=dp(48)); go.bind(on_release=lambda *_: setattr(self.manager, "current", "home")); self.panel.add_widget(go)

    def join_existing(self, *_):
        code = str(getattr(self, "join_code", None).text if hasattr(self, "join_code") else "").strip()
        if not code:
            self.mode_status.text = "Enter the joining code supplied by the business administrator."; return
        if not online_configured():
            self.mode_status.text = "Supabase is not configured. Connect to the cloud before joining."; return
        self.mode_status.text = "Verifying code and device limit with Supabase..."
        def work():
            try:
                data = join_business_with_code(code, device_id())
                reg = {"business_id": str(data["business_id"]), "business_name": str(data.get("business_name") or "My Shop"),
                       "sync_token": str(data["sync_token"]), "device_id": device_id(),
                       "expires_at": str(data.get("expires_at") or ""), "device_role": str(data.get("device_role") or "employee"),
                       "max_devices": data.get("max_devices")}
                save_json("cloud_device_registration.json", reg)
                save_json("pending_license_request.json", None)
                def done(_dt):
                    app = self.manager.app
                    app.accept_new_license(online=True)
                    if app.license_required:
                        self.mode_status.text = app.license_message; return
                    app.license_message = "JOINED BUSINESS\n" + reg["business_name"] + "\nCloud registration confirmed."
                    app._sync_status = "SYNCING"; app._sync_error = ""
                    self.mode_status.text = app.license_message
                    app.schedule_sync(force=True); self.manager.current = "home"
                Clock.schedule_once(done, 0)
            except Exception as exc:
                msg = str(exc)
                Clock.schedule_once(lambda _dt: setattr(self.mode_status, "text", "JOIN FAILED\n" + msg), 0)
        threading.Thread(target=work, daemon=True).start()

    def open_support(self, *_):
        self.show_support()

    def recheck_license(self, *_):
        app = self.manager.app
        self.mode_status.text = "Checking your licence online..."
        def done(outcome):
            if app.license_required and hasattr(self, "mode_status"):
                note = {"offline": "\n(Could not reach the server - check your internet connection.)",
                        "skipped": "\n(Nothing to check online for this phone yet.)"}.get(outcome, "")
                self.mode_status.text = app.license_message + note
        app.check_license_online(on_done=done)

    def on_leave(self,*_):
        if hasattr(self,"poll_event") and self.poll_event:
            self.poll_event.cancel()

    def copy(self,t,s):
        try:
            from kivy.core.clipboard import Clipboard
            Clipboard.copy(t); s.text="Device request copied."
        except Exception as e: s.text=str(e)

    def start_polling(self):
        if hasattr(self,"poll_event") and self.poll_event: self.poll_event.cancel()
        self.poll_event=Clock.schedule_interval(lambda dt:self.check_online(None),5)

    def refresh_support(self):
        # Keep the activation form usable even if support metadata is unavailable.
        if online_configured():
            def work():
                try: fetch_support_online()
                except Exception: pass
            threading.Thread(target=work,daemon=True).start()

    def _submit_blocked(self):
        """True while SUBMIT ACTIVATION REQUEST must stay off: a send in progress, a request already
        waiting at the server, or a license that is still valid."""
        if getattr(self,"_submit_inflight",False): return True
        try:
            if license_status()[0]=="ok": return True
        except Exception: pass
        pending=load_json("pending_license_request.json",None)
        return bool(isinstance(pending,dict) and pending.get("request_token"))

    def _refresh_submit_btn(self):
        btn=getattr(self,"submit_btn",None)
        if btn is not None: btn.disabled=self._submit_blocked()      # label never changes

    def request_online(self,*_):
        # Hard guard besides the disabled button: fast double taps, a request already waiting,
        # or a still-valid license must never create another request.
        if self._submit_blocked():
            self._refresh_submit_btn(); return
        if not online_configured(): self.mode_status.text="ONLINE SERVICE NOT CONFIGURED"; return
        business=self.business_input.text.strip(); contact=self.contact_input.text.strip()
        if not business: self.mode_status.text="BUSINESS NAME REQUIRED"; return
        if not contact: self.mode_status.text="CONTACT NUMBER REQUIRED"; return
        # A business that already has (or had) a license/registration on this phone is asking to RENEW,
        # so the server must file it as a renewal, never as a new business.
        kind="renewal" if (load_saved_license() or _cloud_registration()) else "activation"
        self._submit_inflight=True; self._refresh_submit_btn()      # off immediately, before the network call
        self.mode_status.text="Sending activation request online..."
        def work():
            try:
                ref=submit_online_request(business,contact,kind)[0][:8]
                Clock.schedule_once(lambda dt:self._online_status("REQUEST SENT (Ref "+ref+")\nWaiting for developer approval."),0)
            except Exception as e:
                err=str(e); Clock.schedule_once(lambda dt:self._online_status("ONLINE REQUEST ERROR\n"+err),0)
            finally:
                # Failed send: nothing was saved, so the button re-opens. Successful send: the saved
                # pending request keeps it off.
                def release(dt):
                    self._submit_inflight=False; self._refresh_submit_btn()
                Clock.schedule_once(release,0)
        threading.Thread(target=work,daemon=True).start()

    def _online_status(self,text): self.mode_status.text=text

    def check_online(self,*_):
        if getattr(self,"_check_busy",False): return
        pending=load_json("pending_license_request.json",None)
        if not pending or not pending.get("request_token"):
            if hasattr(self,"mode_status"): self.mode_status.text="No pending online activation request."
            return
        if not online_configured(): self.mode_status.text="ONLINE SERVICE NOT CONFIGURED"; return
        self.mode_status.text="Checking for activation..."; token=pending["request_token"]; self._check_busy=True
        def work():
            try:
                row=poll_online_response(token)
                if not row:
                    Clock.schedule_once(lambda dt:self._online_status("Still waiting for Developer Control approval."),0); return
                if not isinstance(row,dict): raise RuntimeError("Unexpected activation response from server.")
                st=str(row.get("status") or row.get("state") or "").strip().lower()
                if st in ("cancelled","canceled","rejected","declined","denied","withdrawn") and not (row.get("activation_code") or row.get("code") or row.get("license")):
                    # Request was cancelled/rejected: drop it so the button re-opens for a new one.
                    save_json("pending_license_request.json",None)
                    def reopened(_dt):
                        self._refresh_submit_btn()
                        self.mode_status.text="Your request was cancelled. You can submit a new one."
                    Clock.schedule_once(reopened,0); return
                code=str(row.get("activation_code") or row.get("code") or row.get("license") or "").strip()
                if not code: raise RuntimeError("Server returned no activation code.")
                ok,p=verify_license(code)
                if not ok: raise RuntimeError(str(p))
                save_signed_license(code,p); save_json("pending_license_request.json",None)
                def done(_dt):
                    self.manager.app.accept_new_license(online=True)
                    self._refresh_submit_btn()
                    if self.manager.app.license_required:
                        self.mode_status.text=self.manager.app.license_message; return
                    self.manager.app.license_message="ACTIVATED ONLINE\nBusiness: "+str(p.get("business_name",""))+"\nExpires: "+str(p.get("expires_at",""))
                    self.mode_status.text=self.manager.app.license_message; self.manager.current="home"
                Clock.schedule_once(done,0)
            except Exception as e:
                err=str(e); Clock.schedule_once(lambda dt:self._online_status("ONLINE CHECK ERROR\n"+err),0)
            finally: Clock.schedule_once(lambda dt:setattr(self,"_check_busy",False),0)
        threading.Thread(target=work,daemon=True).start()

    def activate(self,b,s):
        code=b.text.strip();ok,p=verify_license(code)
        if ok:
            save_signed_license(code,p);save_json("pending_license_request.json",None)
            self.manager.app.accept_new_license(online=False)
            if self.manager.app.license_required:
                s.text="ACTIVATION REQUIRED\n"+self.manager.app.license_message;return
            self.manager.app.license_message=f"ACTIVATED\nBusiness: {p.get('business_name')}\nExpires: {p.get('expires_at')}"
            s.text=self.manager.app.license_message;self.manager.current="home"
        else:
            self.manager.app.license_required=True;self.manager.app.license_message=str(p);s.text="ACTIVATION REQUIRED\n"+str(p)

class DeviceManagement(Base):
    def on_pre_enter(self, *_):
        self.clear_widgets()
        root = BoxLayout(orientation="vertical", padding=dp(10), spacing=dp(7))
        root.add_widget(self.top("Cloud Devices & Joining Code"))
        info = _sync_license_info()
        if not info:
            root.add_widget(AppLabel(text="This device has no cloud registration. Activate or join a business first.", size_hint_y=None, height=dp(60)))
            self.set_content(root); return
        reg = _cloud_registration() or {}
        role = str(reg.get("device_role") or "owner").lower()
        root.add_widget(AppLabel(text="Business: " + str(reg.get("business_name") or self.shop_name()) + "\nRole: " + role.title(),
                                 size_hint_y=None, height=dp(52), halign="left"))
        self.limit_label = AppLabel(text="Loading device allowance...", size_hint_y=None, height=dp(38))
        root.add_widget(self.limit_label)
        row = GridLayout(cols=3, spacing=dp(5), size_hint_y=None, height=dp(48))
        gen = AppButton(text="GENERATE CODE", font_size=sp(11)); gen.bind(on_release=self.generate); row.add_widget(gen)
        revoke_code = AppButton(text="REVOKE CODE", font_size=sp(11)); revoke_code.bind(on_release=self.revoke_code); row.add_widget(revoke_code)
        refresh = AppButton(text="REFRESH", font_size=sp(11)); refresh.bind(on_release=self.refresh_devices); row.add_widget(refresh); root.add_widget(row)
        self.code_view = AppTextInput(text="", readonly=True, multiline=False, size_hint_y=None, height=dp(64),
                                      font_size=sp(24), halign="center", foreground_color=(0.04,0.16,0.32,1),
                                      background_color=SELECT_BG, cursor_blink=False, use_bubble=False, use_handles=False)
        root.add_widget(self.code_view)
        root.add_widget(AppLabel(text="Codes expire automatically and work once. Read the code aloud or use COPY JOINING CODE.",
                                 font_size=sp(11), size_hint_y=None, height=dp(34)))
        share = AppButton(text="COPY JOINING CODE", size_hint_y=None, height=dp(42)); share.bind(on_release=lambda *_: self.copy_text(self.code_view.text)); root.add_widget(share)
        self.devices_view = AppTextInput(text="", readonly=True, multiline=True, size_hint_y=None, height=dp(190))
        self.autosize_text(self.devices_view, dp(120)); root.add_widget(self.devices_view)
        self.target = AppTextInput(hint_text="Exact device ID to revoke", multiline=False, size_hint_y=None, height=dp(44)); root.add_widget(self.target)
        revoke = AppButton(text="REVOKE DEVICE", size_hint_y=None, height=dp(44)); revoke.bind(on_release=self.revoke); root.add_widget(revoke)
        self.set_content(root)
        self.refresh_devices()

    def _info(self):
        info = _sync_license_info()
        if not info: raise RuntimeError("No active cloud registration found.")
        return info

    def generate(self, *_):
        if getattr(self, "_busy", False): return
        try: info = self._info()
        except Exception as e: self.msg("Could not generate joining code:\n" + str(e)); return
        self._busy = True
        previous = self.limit_label.text
        self.limit_label.text = "Generating code, please wait..."
        def work():
            data = generate_business_join_code(info)
            if not isinstance(data, dict) or not data.get("join_code"):
                raise RuntimeError("Supabase did not return a joining code. Apply the supplied migration first.")
            return data
        def done(data):
            self._busy = False
            self.code_view.text = str(data["join_code"])
            try: self.manager.app.fast_sync()
            except Exception: pass
            self.limit_label.text = "Device slots used: " + str(data.get("active_devices", "?")) + " / " + str(data.get("max_devices", "?"))
            self.msg("A new single-use code was generated. Any previous unused code has been invalidated.")
        def fail(e):
            self._busy = False
            self.limit_label.text = previous
            self.msg("Could not generate joining code:\n" + str(e))
        self.run_bg(work, done, fail)

    def revoke_code(self, *_):
        if getattr(self, "_busy", False): return
        try: info = self._info()
        except Exception as e: self.msg("Could not revoke joining code:\n" + str(e)); return
        self._busy = True
        previous = self.limit_label.text
        self.limit_label.text = "Revoking code, please wait..."
        def done(result):
            self._busy = False
            self.limit_label.text = previous
            self.code_view.text = ""
            self.msg("Unused joining codes have been revoked. Existing registered devices remain connected.\n" + str(result))
        def fail(e):
            self._busy = False
            self.limit_label.text = previous
            self.msg("Could not revoke joining code:\n" + str(e))
        self.run_bg(lambda: revoke_business_join_code(info), done, fail)

    def refresh_devices(self, *_):
        try: info = self._info()
        except Exception as e: self.devices_view.text = "Could not load devices.\n" + str(e); return
        self.devices_view.text = "Loading devices..."
        def done(rows):
            try:
                self.devices_view.text = "\n\n".join(
                    "Device: {device_id}\nName: {device_name}\nRole: {device_role}\nStatus: {status}\nRegistered: {registered_at}\nLast seen: {last_seen_at}".format(**{k: r.get(k, "-") for k in ("device_id","device_name","device_role","status","registered_at","last_seen_at")})
                    for r in rows if isinstance(r, dict)) or "No devices returned."
                reg = _cloud_registration() or {}
                max_devices = reg.get("max_devices")
                if max_devices is not None: self.limit_label.text = "Registered devices: " + str(len([r for r in rows if r.get("status") == "active"])) + " / " + str(max_devices)
            except Exception as e: self.devices_view.text = "Could not load devices.\n" + str(e)
        def fail(e): self.devices_view.text = "Could not load devices.\n" + str(e)
        self.run_bg(lambda: list_business_devices(info), done, fail)

    def revoke(self, *_):
        if getattr(self, "_busy", False): return
        target = self.target.text.strip()
        if not target: self.msg("Enter the exact device ID to revoke."); return
        try: info = self._info()
        except Exception as e: self.msg("Could not revoke device:\n" + str(e)); return
        self._busy = True
        def done(_result):
            self._busy = False
            self.msg("Device revocation submitted to Supabase."); self.refresh_devices()
        def fail(e):
            self._busy = False
            self.msg("Could not revoke device:\n" + str(e))
        self.run_bg(lambda: revoke_business_device(info, target), done, fail)


# ===================== FINANCE SCREENS (BEGIN) =====================
FIN_W = 36


def fin_sync_line(app):
    """Visible sync status for financial records (single-phone businesses stay local-only)."""
    line = app.sync_summary()
    st = load_json("sync_ledger_status.json", {})
    if isinstance(st, dict) and st.get("error"):
        line += "\nFinancial ledger NOT synced: " + str(st["error"])[:140]
    return line


def fin_report_text(c, label, W=FIN_W):
    """The one text layout used by the dashboard (and reused by statements)."""
    f, l, p = c["period"], c["lifetime"], c["position"]
    setup = c["setup_done"]
    rule = "-" * W
    row = lambda a, v: _lr(a, num(v), W)
    need = lambda v: num(v) if setup else "not set"
    out = []
    out += ["THIS PERIOD: " + label, rule,
            row("Gross sales", f["gross_sales"]), row("- Discounts", f["discounts"]),
            row("- Sales returns", f["returns"]), row("= Net sales", f["net_sales"]),
            row("- Cost of goods sold", f["cogs"]), row("= GROSS PROFIT", f["gross_profit"]),
            _lr("  Gross margin", ("%.1f%%" % f["gross_margin_pct"]) if f["gross_margin_pct"] is not None else "n/a", W),
            row("- Operating expenses", f["operating_expenses"])]
    for name, v in f["other_breakdown"].items():
        if abs(v) > 0.004:
            out.append(row("  - " + name, v))
    out += [row("- Other costs (total)", f["other_costs"]), rule, row("NET PROFIT / (LOSS)", f["net_profit"]), rule,
            row("Cash received, sales", f["cash_from_sales"]), row("Debts collected (cash in)", f["collections"]),
            row("Paid to suppliers (cash out)", f["debts_paid"]),
            row("Profit left after clearing debts", f["net_profit"] - f["debts_paid"]),
            row("Stock bought", f["stock_purchased"]), row("  paid now", f["stock_purchased_paid"]),
            row("  on credit", f["stock_purchased_credit"]),
            row("Owner investments", f["owner_investments"]), row("Owner withdrawals", f["owner_withdrawals"])]
    if f["break_even_sales"] is not None:
        out.append(row("Break-even sales*", f["break_even_sales"]))
    now = c["end"] > today_date()
    out += ["", ("CURRENT POSITION (balances, not daily)" if now else "POSITION AT END OF PERIOD"), rule,
            row("Shop cash", p["cash"]), row("Inventory at cost", p["inventory"]),
            row("Customers owe us", p["receivables"]), row("Equipment", p["equipment"]), row("Other assets", p["other_assets"]),
            _lr("TOTAL ASSETS", need(p["total_assets"]), W), rule,
            row("We owe suppliers", p["payables"]), row("Other liabilities", p["other_liabilities"]), row("TOTAL LIABILITIES", p["total_liabilities"]), rule,
            _lr("NET BUSINESS CAPITAL", need(p["net_capital"]), W),
            _lr("WORKING CAPITAL", need(p["working_capital"]), W)]
    out += service_recovery_lines(c.get("service_recovery"), W)
    out += ["", "CAPITAL MOVEMENT (lifetime)", rule,
            row("Opening net assets (calculated equity)", p["opening_equity"]), row("+ Additional investments", l["owner_investments"]),
            row("+ Net profit / - loss", l["net_profit"]), row("- Owner withdrawals", l["owner_withdrawals"])]
    if abs(p.get("stock_difference", 0.0)) > FIN_TOLERANCE:
        out.append(row("+ Stock difference (shelves vs books)", p["stock_difference"]))
    out += [row("= Ending capital", p["ending_equity"]), row("Total stock purchased", l["stock_purchased"])]
    if setup:
        d = p["equity_difference"]
        out.append(_lr("Balance sheet difference", num(d), W))
        if abs(d) > FIN_TOLERANCE:
            out += ["  DISCREPANCY: tap RECONCILE to find", "  it. Nothing was adjusted automatically."]
    out += ["", "Inventory is valued at cost, never at", "selling price. Credit sales are not cash", "until collected. Loans and owner money",
            "are never counted as profit.",
            "* Break-even treats all expenses as fixed."]
    return _wrap_report("\n".join(out), W)


def fin_investment_text(db, W=FIN_W):
    """Starting position, accounting profit and payback, all derived by the engine (nothing keyed in)."""
    r = fin_investment(db)
    o, rule = r["opening"], "-" * W
    row = lambda a, v: _lr(a, num(v), W)
    pct = lambda v: ("%.1f%%" % v) if v is not None else "n/a"
    started = r["started_on"].strftime("%d/%m/%Y") if r["started_on"] else "not yet"
    if r["total_invested"] <= 0:
        payback = "n/a"
    elif r["still_to_recover"] <= 0.004:
        payback = "RECOVERED"
    elif r["payback_months_left"] is None:
        payback = "no profit pace yet"
    elif r["payback_months_left"] >= 24:
        payback = "%.1f years left" % (r["payback_months_left"] / 12.0)
    else:
        payback = "%.1f months left" % r["payback_months_left"]
    out = ["STARTING POSITION (automatic)", rule,
           row("Stock at cost (opening stock)", o["inventory"]), row("Cash at start", o["cash"]),
           row("Equipment / fixtures", o["equipment"]), row("Other assets", o["other_assets"]),
           row("Customers owed us", o["receivables"]), row("- Owed to suppliers", o["payables"] + o["other_liabilities"]), rule,
           row("= WORTH WHEN YOU STARTED", r["starting_worth"]), _lr("Using the app since", started, W),
           "", "PROFIT, ACCOUNTING BASIS (all time)", rule,
           row("Operating profit", r["operating_profit"]),
           row("- Other costs & write-offs", r["operating_profit"] - r["accounting_profit"]), rule,
           row("= ACCOUNTING PROFIT", r["accounting_profit"]),
           "", "INVESTMENT & PAYBACK", rule,
           row("Starting worth", r["starting_worth"]), row("+ Owner money added", r["owner_investments"]),
           row("= TOTAL INVESTED", r["total_invested"]),
           row("Investment recovered (cash profit)", r["recovered"]), _lr("  recovered so far", pct(r["payback_pct"]), W),
           row("Still to recover", r["still_to_recover"]),
           row("Average cash profit / month", r["avg_monthly_cash_profit"]), _lr("Payback", payback, W),
           _lr("Return on investment", pct(r["roi_pct"]), W),
           _lr("  at yearly pace", pct(r["roi_yearly_pace_pct"]), W),
           row("Owner took out", r["owner_drawings"]), row("Profit kept in business", r["profit_kept"]),
           row("Worth now", r["worth_now"]), row("Growth since start", r["growth_since_start"])]
    if r["auto_funded"] > 0.004:
        out.append(_lr("  incl. funded automatically", num(r["auto_funded"]), W))
    if r["months"]:
        out += ["", "LAST MONTHS", rule]
        out += [_lr(m["month"] + "  sales " + num(m["net_sales"]), "profit " + num(m["accounting_profit"]), W) for m in r["months"]]
    out += ["", "Payback = profit / total invested. Equipment wear is", "not charged here: see Equipment Replacement Plan."]
    return _wrap_report("\n".join(out), W)


def fin_form(screen, title, help_text, fields, save_fn):
    """Generic one-screen form. fields: (key, label, kind, extra). Each open gets one dedupe key,
    so a double-tap or retry can never post the same transaction twice."""
    import uuid as _uuid
    db = screen.manager.app.db
    box = BoxLayout(orientation="vertical", padding=dp(8), spacing=dp(5), size_hint_y=None)
    if help_text:
        h = AppLabel(text=help_text, font_size=sp(11), size_hint_y=None, height=dp(74), halign="left", valign="middle")
        h.bind(width=lambda i, w: setattr(i, "text_size", (w, None)))
        h.bind(texture_size=lambda i, ts: setattr(i, "height", max(dp(74), ts[1] + dp(8))))
        box.add_widget(h)
    widgets = {}
    for key, label, kind, extra in fields:
        lab = AppLabel(text=label, size_hint_y=None, height=dp(22), font_size=sp(11), halign="left", bold=True)
        lab.bind(width=lambda i, w: setattr(i, "text_size", (w, None)))
        box.add_widget(lab)
        if kind == "amount":
            w = AppTextInput(text=str(extra or ""), hint_text=label, multiline=False, input_filter="float", size_hint_y=None, height=dp(44))
        elif kind == "text":
            w = AppTextInput(text=str(extra or ""), hint_text=label, multiline=False, size_hint_y=None, height=dp(44))
        elif kind == "method":
            w = AppSpinner(text=str(extra or "cash"), values=CASH_ACCOUNTS, size_hint_y=None, height=dp(44))
        elif kind == "choice":
            w = AppSpinner(text=str(extra[0]), values=tuple(str(x) for x in extra), size_hint_y=None, height=dp(44))
        elif kind == "product":
            search = AppTextInput(hint_text="Search product name...", multiline=False, size_hint_y=None, height=dp(44))
            w = AppSpinner(text="Tap to choose product", values=(), size_hint_y=None, height=dp(44))
            w._map = {}

            def refill(_i=None, _t=None, w=w, search=search, any_stock=(extra == "any")):
                q = normalize_product_name(search.text)
                w._map = {}
                for p in db.products:
                    if safe_float(p.get("qty")) <= 0 and not any_stock:
                        continue
                    hay = normalize_product_name(" ".join(str(p.get(k) or "") for k in ("name", "brand", "variant", "product_class")))
                    if q and q not in hay:
                        continue
                    lbl = " | ".join(x for x in (str(p.get("name", "")), str(p.get("brand") or ""), str(p.get("variant") or "")) if x) \
                        + f" | stock {safe_float(p.get('qty')):g}"
                    w._map[lbl] = p
                    if len(w._map) >= 30:
                        break
                w.values = tuple(w._map.keys())
                if q and len(w._map) == 1:
                    w.text = next(iter(w._map))
            search.bind(text=refill)
            refill()
            box.add_widget(search)
        else:
            raise ValueError("bad field kind")
        widgets[key] = w
        box.add_widget(w)
    status = AppLabel(text="", size_hint_y=None, height=dp(44), font_size=sp(11), color=DANGER, halign="left", valign="middle")
    status.bind(width=lambda i, w: setattr(i, "text_size", (w, None)))
    save = AppButton(text="SAVE", size_hint_y=None, height=dp(46), background_color=SUCCESS)
    cancel = AppButton(text="CANCEL", size_hint_y=None, height=dp(42), background_color=GREY)
    box.add_widget(status); box.add_widget(save); box.add_widget(cancel)
    popup = Popup(title=screen.shop_name() + " - " + title, content=screen.scroll_wrap(box), size_hint=(.96, .92))
    key = "form:" + _uuid.uuid4().hex
    state = {"busy": False}

    def vals():
        out = {}
        for k, w in widgets.items():
            out[k] = (w._map.get(w.text) if hasattr(w, "_map") else w.text)
        return out

    def do_save(*_):
        if state["busy"]:
            return
        state["busy"] = True
        try:
            result = save_fn(vals(), key)
            db.save()
            popup.dismiss()
            if hasattr(screen, "on_pre_enter"):
                screen.on_pre_enter()
            screen.msg(result or "Saved.")
            Clock.schedule_once(lambda dt: fin_prompt_funding_remark(screen), 0.6)
        except Exception as e:
            state["busy"] = False
            status.text = str(e)

    save.bind(on_release=do_save)
    cancel.bind(on_release=lambda *_: popup.dismiss())
    popup.open()


def fin_no_debt_help(screen, who):
    """Pay Supplier / Customer Pays Debt when nothing is owed yet: explain where debts are
    recorded and offer one-tap shortcuts (instead of a dead-end one-line message)."""
    if who == "supplier":
        title = "Pay supplier"
        body = ("No supplier debts are recorded yet.\n\n"
                "A supplier debt is created when you stock a product on credit:\n"
                "1. Open Products, then add a product or restock one.\n"
                "2. Enter the Supplier name and the amount Paid now (0 = all on credit).\n\n"
                "The debt then appears here and on the dashboard, and you can record each payment you make.\n\n"
                "Use Record Debt below to enter a supplier balance that existed before you started using the app.")
        go_text, go_screen = "Open Products", "products"
    else:
        title = "Customer debt payment"
        body = ("No customer debts are recorded yet.\n\n"
                "A customer debt is created at the Sale screen: when a customer pays less than the total, "
                "type the customer's name before completing the sale. The balance is recorded as a credit sale.\n\n"
                "The debt then appears here and on the dashboard, and you can record each payment you receive.\n\n"
                "Use Record Debt below to enter a customer balance that existed before you started using the app.")
        go_text, go_screen = "Open Sale Screen", "sale"
    box = BoxLayout(orientation="vertical", padding=dp(10), spacing=dp(8))
    text = wrap_label(body, font_size=sp(13))
    sv = SmoothScroll(do_scroll_x=False, bar_width=dp(4))
    sv.add_widget(text)
    box.add_widget(sv)
    go = AppButton(text=go_text, size_hint_y=None, height=dp(46))
    close = AppButton(text="Close", size_hint_y=None, height=dp(42))
    for b in (go, close):
        box.add_widget(b)
    popup = Popup(title=screen.shop_name() + " - " + title, content=box, size_hint=(.94, .82))
    close.bind(on_release=lambda *_: popup.dismiss())

    def go_there(*_):
        popup.dismiss()
        screen.manager.current = go_screen

    go.bind(on_release=go_there)
    popup.open()


def fin_show_debt_history(screen, who):
    db = screen.manager.app.db
    title, rows = fin_detail(db, "customers" if who == "customer" else "suppliers", None, today_date() + timedelta(days=1))
    lines = [title, "As at today (all time)", "-" * 40]
    total = 0.0
    for d, text, a in rows:
        total += a
        lines.append(f"{short_stamp(d) if d else 'opening     '}  {str(text)[:22]:<22} {num(a):>10}")
    if not rows:
        lines.append("No records.")
    lines += ["-" * 40, _lr("TOTAL (" + str(len(rows)) + " rows)", num(total), 40)]
    screen.show_text_popup("\n".join(lines), "Details")


def fin_debt_hub(screen, who):
    """Customers who owe you / suppliers you owe: every name with its balance. Tap a name to record
    a payment; Record Debt adds an older or outside debt; View History lists every movement."""
    db = screen.manager.app.db
    cust = (who == "customer")
    c = fin_compute(db)
    balances = c["customers"] if cust else c["suppliers"]
    owed = sorted(((n, v) for n, v in balances.items() if v > 0.004), key=lambda x: -x[1])
    total = sum(v for _, v in owed)
    colour = SUCCESS if cust else DANGER
    box = BoxLayout(orientation="vertical", padding=dp(10), spacing=dp(8))
    box.add_widget(wrap_label(fin_fmt(total), font_size=sp(24), bold=True, color=colour, min_h=dp(34)))
    box.add_widget(wrap_label(str(len(owed)) + (" customer" if cust else " supplier") + ("" if len(owed) == 1 else "s")
                              + " with an unpaid balance", font_size=sp(12), color=TEXT_MUTED))
    rows = BoxLayout(orientation="vertical", size_hint_y=None, spacing=dp(6))
    rows.bind(minimum_height=rows.setter("height"))
    if not owed:
        rows.add_widget(wrap_label(
            ("No customer debts" if cust else "No supplier debts") + " are recorded yet.\n\n"
            + ("A customer debt is created automatically at the Sale screen when the customer pays less than the total and you type their name.\n\n"
               if cust else
               "A supplier debt is created automatically when you stock a product on credit (enter the supplier and the amount Paid now).\n\n")
            + "Use Record Debt below for money that was already owed before you started using this app.", font_size=sp(13)))
    for name, amount in owed:
        row = ActionCard(orientation="horizontal", size_hint_y=None, height=dp(58), padding=(dp(12), dp(6)), spacing=dp(8))
        nl = AppLabel(text=name, bold=True, font_size=sp(14), halign="left", valign="middle", shorten=True, shorten_from="right")
        nl.bind(size=lambda i, v: setattr(i, "text_size", (v[0], v[1])))
        al = AppLabel(text=fin_fmt(amount), bold=True, font_size=sp(14), color=colour, halign="right", valign="middle",
                      size_hint_x=None, width=dp(110))
        al.bind(size=lambda i, v: setattr(i, "text_size", (v[0], v[1])))
        row.add_widget(nl)
        row.add_widget(al)
        row.add_widget(AppLabel(text="\u203a", font_size=sp(24), color=GREY, size_hint_x=None, width=dp(16)))
        row.bind(on_release=lambda _w, n=name: (popup.dismiss(), Clock.schedule_once(
            lambda dt: fin_open_form(screen, "cust_pay" if cust else "pay_supplier", party=n), 0)))
        rows.add_widget(row)
    sv = SmoothScroll(do_scroll_x=False, bar_width=dp(4))
    sv.add_widget(rows)
    box.add_widget(sv)
    if owed:
        box.add_widget(wrap_label("Tap a name to record a payment " + ("received." if cust else "you made."),
                                  font_size=sp(11), color=TEXT_MUTED))
    top_row = GridLayout(cols=2, spacing=dp(8), size_hint_y=None, height=dp(48))
    rec = AppButton(text="Record Debt")
    hist = AppButton(text="View History", background_color=INFO)
    top_row.add_widget(rec)
    top_row.add_widget(hist)
    close = AppButton(text="Close", size_hint_y=None, height=dp(46))
    box.add_widget(top_row)
    box.add_widget(close)
    popup = Popup(title=screen.shop_name() + " - " + ("Customers who owe you" if cust else "Suppliers you owe"),
                  content=box, size_hint=(.94, .88))
    rec.bind(on_release=lambda *_: (popup.dismiss(), Clock.schedule_once(
        lambda dt: fin_open_form(screen, "debt_customer" if cust else "debt_supplier"), 0)))
    hist.bind(on_release=lambda *_: fin_show_debt_history(screen, who))
    close.bind(on_release=lambda *_: popup.dismiss())
    popup.open()


def save_owner_withdrawal(v, dedupe_key, post, db):
    amount = safe_float(v["amount"])
    post({"type": "owner_withdrawal", "amount": amount, "method": v["method"], "note": v["note"]}, dedupe_key)
    _, withdrawn = fin_owner_totals(db)
    profit = max(fin_pnl(db)["net_profit"], 0.0)
    message = "Withdrawal of " + fin_fmt(amount) + " recorded."
    if withdrawn > profit + 0.005:
        message += " WARNING: cumulative owner withdrawals exceed accumulated net profit; the excess is consuming existing business capital."
    return message


def fin_open_form(screen, kind, party=None):
    """Opens the right form for a financial event. All saving goes through fin_post()."""
    db = screen.manager.app.db
    c = fin_compute(db)
    owed_sup = [k for k, v in c["suppliers"].items() if v > 0.004]
    owed_cus = [k for k, v in c["customers"].items() if v > 0.004]
    if party in owed_sup:
        owed_sup = [party] + [x for x in owed_sup if x != party]
    if party in owed_cus:
        owed_cus = [party] + [x for x in owed_cus if x != party]
    amt = lambda label="Amount": ("amount", label, "amount", None)
    meth = lambda label="Money goes through": ("method", label, "method", "cash")
    note = lambda label="Note (optional)": ("note", label, "text", "")
    post = lambda e, k: fin_post(db, e, dedupe_key=k)
    ref_note = lambda v: ((("Ref " + str(v.get("ref", "")).strip() + ". ") if str(v.get("ref", "")).strip() else "")
                          + str(v.get("note", "")).strip()).strip()

    def settle(v, k, typ, label, bal_kind):
        amount = safe_float(v["amount"])
        post({"type": typ, "party": v["party"], "amount": amount, "method": v["method"], "note": ref_note(v)}, k)
        left = max(fin_party_balances(db, bal_kind).get(v["party"], 0.0), 0.0)
        return (label + " of " + fin_fmt(amount) + " recorded.\n" + v["party"]
                + (" now owes you " if bal_kind == "customer" else " is now owed ") + fin_fmt(left) + ".")
    pos = c["position"]

    if kind == "withdraw":
        fin_form(screen, "Owner takes money", "Money taken out of the shop. It reduces shop cash and owner capital. It is NOT a shop expense and does not reduce profit.",
                 [amt(), meth("Taken from shop cash"), note("Reason")],
                 lambda v, k: save_owner_withdrawal(v, k, post, db))
    elif kind == "pay_supplier":
        if not owed_sup:
            return fin_debt_hub(screen, "supplier")
        fin_form(screen, "Pay supplier", "Reduces cash and what you owe. This is NOT a new purchase and NOT an expense.\n"
                 + "\n".join(f"{n}: {fin_fmt(c['suppliers'][n])}" for n in owed_sup[:6]),
                 [("party", "Supplier", "choice", owed_sup), amt("Amount paid"), meth("Paid from"),
                  ("ref", "Receipt / reference (optional)", "text", ""), note()],
                 lambda v, k: settle(v, k, "supplier_payment", "Supplier payment", "supplier"))
    elif kind == "cust_pay":
        if not owed_cus:
            return fin_debt_hub(screen, "customer")
        fin_form(screen, "Customer payment", "Money collected from a customer who bought on credit. Not new sales.\n"
                 + "\n".join(f"{n}: {fin_fmt(c['customers'][n])}" for n in owed_cus[:6]),
                 [("party", "Customer", "choice", owed_cus), amt("Amount received"), meth("Received into"),
                  ("ref", "Receipt / reference (optional)", "text", ""), note()],
                 lambda v, k: settle(v, k, "customer_payment", "Payment", "customer"))
    elif kind in ("debt_supplier", "debt_customer"):
        sup = (kind == "debt_supplier")
        fin_form(screen, "Record supplier debt" if sup else "Record customer debt",
                 ("Money you owe a supplier" if sup else "Money a customer owes you")
                 + " that is not already recorded by a sale or restock in this app: for example an old debt from before you started "
                 "using the app. It adds to the balance and adjusts your opening capital by the same amount, so your books stay "
                 "balanced. Nothing is added to sales, expenses or cash.\nNew credit "
                 + ("restocks (Products: supplier name + Paid now)" if sup else "sales (Sale screen: customer name)")
                 + " are recorded automatically; do not enter them here.",
                 [("party", "Supplier name" if sup else "Customer name", "text", ""), amt("Amount owed"),
                  ("note", "What is this debt for? (optional)", "text", ""), ("ref", "Invoice / reference (optional)", "text", "")],
                 lambda v, k: (post({"type": "debt_forward", "kind": "supplier" if sup else "customer",
                                     "party": v["party"].strip(), "amount": safe_float(v["amount"]), "note": ref_note(v)}, k),
                               "Debt of " + fin_fmt(safe_float(v["amount"])) + " recorded for " + v["party"].strip() + ".")[1])
    elif kind == "equipment":
        OWNED = "Already owned / brought in by owner"
        BOUGHT = "Bought now with shop money"

        def save_equipment(v, k):
            name, cost = v["note"].strip(), safe_float(v["amount"])
            if not name:
                raise ValueError("Say what the equipment is.")
            if cost <= 0:
                raise ValueError("Type the cost or value.")
            e = {"type": "equipment_purchase", "amount": cost, "method": "cash", "note": name}
            if v["life"] != "default":
                e["life_years"] = float(v["life"])
            if v["how"] == OWNED:
                # The business owns it but no shop money was spent: owner puts in the item, cash stays the same.
                post({"type": "owner_investment", "amount": cost, "method": "cash", "bundle": k,
                      "note": "Equipment brought in by owner: " + name}, k + ":in")
                e["bundle"] = k
                post(e, k + ":eq")
                return name + " added. No shop money was used."
            post(e, k + ":eq")
            return name + " added. Shop cash went down by " + fin_fmt(cost) + "."
        fin_form(screen, "Add equipment / asset",
                 "Shelves, fridge, scale and so on. Choose how the business got it. Cash is never typed in by hand: "
                 "if you spend more than the shop has, the shop notes the difference as your money and asks you for a remark.",
                 [("note", "What is it?", "text", ""), amt("Cost or value"),
                  ("how", "How did the business get it?", "choice", (BOUGHT, OWNED)),
                  ("life", "How many years will it last?", "choice", ("default", "1", "2", "3", "5", "10"))], save_equipment)
    elif kind == "equipment_replace":
        assets = Books(db).replacement_plan()["assets"]
        if not assets:
            screen.msg("No equipment recorded yet. Add equipment first.")
            return
        labels = {}
        for a in assets:
            labels[a["name"] + " | cost " + fin_fmt(a["cost"]) + " | " + a["bought"].strftime("%d/%m/%Y")] = a

        def save_replace(v, k):
            old = labels.get(v["old"])
            name, new_cost, got = v["note"].strip(), safe_float(v["amount"]), safe_float(v["proceeds"])
            if old is None:
                raise ValueError("Choose the equipment you are replacing.")
            if not name:
                raise ValueError("Say what the new equipment is.")
            if new_cost <= 0:
                raise ValueError("Type the cost of the new equipment.")
            e = {"type": "equipment_replacement", "amount": new_cost, "proceeds": got, "method": "cash",
                 "old_ref": old["id"], "note": name}
            if safe_float(v["old_cost"]) > 0:
                e["old_cost"] = safe_float(v["old_cost"])
            if v["life"] != "default":
                e["life_years"] = float(v["life"])
            saved, _ = post(e, k)
            diff = saved["old_cost"] - got
            net = new_cost - got
            return (old["name"] + " replaced by " + name + ".\n"
                    + (("Loss on the old equipment: " if diff >= 0 else "Gain on the old equipment: ") + fin_fmt(abs(diff)) + ".\n")
                    + (("Shop cash went down by " if net >= 0 else "Shop cash went up by ") + fin_fmt(abs(net)) + "."))
        fin_form(screen, "Replace / upgrade equipment",
                 "The old equipment leaves your list and is sold at the price you type. The new one is added at its cost. "
                 "If the old one sold for less than it cost, the difference is shown as a LOSS in your profit statement "
                 "(a gain if it sold for more). Shop cash changes only by new cost minus the money you got.",
                 [("old", "Which equipment is being replaced?", "choice", tuple(labels.keys())),
                  ("proceeds", "Price the old equipment sold for (0 if given away)", "amount", "0"),
                  ("old_cost", "Old cost (only if it is part of a bigger opening amount)", "amount", ""),
                  ("note", "New equipment name", "text", ""), amt("Cost of the new equipment"),
                  ("life", "How many years will the new one last?", "choice", ("default", "1", "2", "3", "5", "10"))],
                 save_replace)
    elif kind == "other_cost":
        fin_form(screen, "Other business cost / tax", "Other shop costs such as tax, licences or fees. Reduces profit.",
                 [("category", "Type", "choice", ("Tax", "Licence / fees", "Other")),
                  amt(), meth("Paid from"), note()],
                 lambda v, k: (post({"type": "other_cost", "amount": safe_float(v["amount"]), "method": v["method"],
                                     "category": v["category"], "note": (v["category"] + ": " + v["note"]).strip(": ")}, k), "Cost recorded.")[1])
    elif kind == "writeoff":
        fin_form(screen, "Stock write-off", "Damaged, expired or lost stock. It leaves inventory and becomes a business loss at its cost.",
                 [("product", "Product", "product", None), ("qty", "Quantity lost", "amount", None), note("Reason (required)")],
                 lambda v, k: (post({"type": "stock_writeoff", "product_pid": (v["product"] or {}).get("pid", ""),
                                     "product": (v["product"] or {}).get("name", ""), "qty": safe_float(v["qty"]), "note": v["note"]}, k),
                               "Write-off recorded.")[1] if v["product"] and v["note"].strip() else (_ for _ in ()).throw(ValueError("Choose a product and give a reason.")))
    elif kind == "return":
        def save_return(v, k):
            p = v["product"]
            if not p:
                raise ValueError("Choose the product returned.")
            last = next((s for s in reversed(db.sales) if str(s.get("product", "")) == str(p.get("name", ""))), None)
            unit_cost = safe_float(last.get("unit_cost")) if last and last.get("unit_cost") is not None else safe_float(p.get("buy"))
            paid = v["settles"].startswith("refund")
            post({"type": "sales_return", "product_pid": p.get("pid", ""), "product": p.get("name", ""), "qty": safe_float(v["qty"]),
                  "amount": safe_float(v["amount"]), "restock": v["restock"].startswith("yes"), "unit_cost": unit_cost,
                  "settles": "paid" if paid else "receivable", "method": v["method"], "party": v["party"], "note": v["note"]}, k)
            return "Return recorded."
        fin_form(screen, "Sales return", "Reduces sales. If the item goes back on the shelf, its cost leaves cost of goods sold. Refund reduces cash; 'off customer balance' reduces what they owe.",
                 [("product", "Product returned", "product", "any"), ("qty", "Quantity", "amount", None), amt("Value refunded / credited"),
                  ("restock", "Put back in stock?", "choice", ("yes - resellable", "no - damaged")),
                  ("settles", "How settled", "choice", ("refund money", "off customer balance")), meth("Refund from"),
                  ("party", "Customer (optional)", "text", ""), note()], save_return)
    elif kind == "discount":
        fin_form(screen, "Sales discount", "A price reduction given to a customer after the sale was recorded. Lowers net sales and profit.",
                 [amt("Discount amount"), ("settles", "Taken from shop cash", "choice", ("paid", "receivable")), meth("If paid: account reduced"),
                  ("party", "Customer (optional)", "text", ""), note("Receipt number / note")],
                 lambda v, k: (post({"type": "sales_discount", "amount": safe_float(v["amount"]), "settles": v["settles"], "method": v["method"],
                                     "party": v["party"], "note": v["note"]}, k), "Discount recorded.")[1])



class FinanceDashboard(Base):
    """Business Capital & Financial Summary. Every figure comes from fin_compute()."""
    range_kind = "today"

    def set_range(self, kind):
        self.range_kind = kind
        self.on_pre_enter()

    def bounds(self):
        t = today_date()
        one = timedelta(days=1)
        k = self.range_kind
        if k == "today":
            return t, t + one, "TODAY " + t.isoformat()
        if k == "week":
            return week_start(t), t + one, "THIS WEEK (from " + week_start(t).isoformat() + ")"
        if k == "month":
            return month_start(t), t + one, "THIS MONTH (from " + month_start(t).isoformat() + ")"
        return None, t + one, "ALL TIME"

    def on_pre_enter(self, *_):
        self.clear_widgets()
        app = self.manager.app
        db = app.db
        start, end, label = self.bounds()
        c = fin_compute(db, start, end)
        layout = BoxLayout(orientation="vertical", padding=dp(8), spacing=dp(6))
        layout.add_widget(self.top("Business Capital"))
        layout.add_widget(AppLabel(text=self.shop_name(), bold=True, font_size=sp(19), size_hint_y=None, height=dp(34)))
        sync = AppLabel(text=fin_sync_line(app), font_size=sp(11), size_hint_y=None, height=dp(48), halign="center", valign="middle")
        sync.bind(width=lambda i, w: setattr(i, "text_size", (w, None)))
        layout.add_widget(sync)
        rng = GridLayout(cols=4, spacing=dp(4), size_hint_y=None, height=dp(42))
        for text, kind in (("TODAY", "today"), ("WEEK", "week"), ("MONTH", "month"), ("ALL", "all")):
            b = AppButton(text=text, font_size=sp(12), background_color=(PRIMARY if self.range_kind == kind else GREY))
            b.bind(on_release=lambda _b, k=kind: self.set_range(k))
            rng.add_widget(b)
        layout.add_widget(rng)
        font = mono_font()
        view = AppTextInput(readonly=True, multiline=True, font_size=sp(12), **({"font_name": font} if font else {}))
        view.text = fin_report_text(c, label)
        self.autosize_text(view, dp(500))
        layout.add_widget(view)

        # Who owes who: always visible, tap a card for the names and amounts.
        class _Dummy:
            text = ""
        layout.add_widget(AppLabel(text="DEBTS (WHO OWES WHO)", bold=True, font_size=sp(12), size_hint_y=None, height=dp(28)))
        debts = GridLayout(cols=2, spacing=dp(8), size_hint_y=None, height=dp(100))
        owed_pos = c["position"]
        for dtitle, amount, count, noun, dkey, dcolor in (
                ("Customers owe you", owed_pos["receivables"], len(c["customers"]), "customer", "Customer debts", SUCCESS),
                ("You owe suppliers", owed_pos["payables"], len(c["suppliers"]), "supplier", "Supplier debts", DANGER)):
            dcard = ActionCard(orientation="vertical", padding=dp(10), spacing=dp(2))
            for text_, size_, bold_, color_ in ((dtitle, 12, False, TEXT_MUTED), (fin_fmt(amount), 17, True, dcolor),
                                                (str(count) + " " + noun + ("" if count == 1 else "s") + "  \u2022  tap to manage", 11, False, TEXT_MUTED)):
                dl = AppLabel(text=text_, font_size=sp(size_), bold=bold_, color=color_, halign="left", valign="middle")
                dl.bind(size=lambda i, v: setattr(i, "text_size", (v[0], v[1])))
                dcard.add_widget(dl)
            dcard.bind(on_release=lambda _w, k=dkey: fin_debt_hub(self, "customer" if k == "Customer debts" else "supplier"))
            debts.add_widget(dcard)
        layout.add_widget(debts)
        layout.add_widget(AppLabel(text="SEE THE TRANSACTIONS BEHIND A FIGURE", bold=True, font_size=sp(12), size_hint_y=None, height=dp(28)))
        self._detail_keys = [("Gross sales", "sales"), ("Cost of goods sold", "cogs"), ("Operating expenses", "expenses"),
                             ("Stock purchases", "purchases"), ("Discounts", "discounts"), ("Sales returns", "returns"),
                             ("Other costs", "other_costs"), ("Owner investments / withdrawals", "owner"),
                             ("Shop cash movements", "cash"),
                             ("Customer debts", "customers"), ("Supplier debts", "suppliers"), ("Inventory at cost", "inventory")]
        pick = AppSpinner(text="Choose a figure...", values=tuple(n for n, _ in self._detail_keys), size_hint_y=None, height=dp(44))
        pick.bind(text=lambda inst, val: self.show_detail(val, inst, start, end))
        layout.add_widget(pick)

        # No Financial Setup: the books follow actual shop transactions only.
        # Three full-width, identical action buttons: same fixed height and font size.
        transaction_options = {
            "Add equipment / asset": "equipment", "Replace / upgrade equipment": "equipment_replace",
            "Owner takes money": "withdraw",
            "Pay supplier": "pay_supplier", "Customer pays debt": "cust_pay",
            "Other business cost": "other_cost", "Stock write-off": "writeoff",
            "Sales return": "return", "Sales discount": "discount"
        }
        finance_actions = BoxLayout(orientation="vertical", spacing=dp(12),
                                    size_hint_y=None, height=dp((4 + (1 if fin_funding_pending(db) else 0)) * 54 + (3 + (1 if fin_funding_pending(db) else 0)) * 12),
                                    padding=(dp(6), 0))

        # Round (pill) buttons: radius is larger than half the height, so the ends are fully rounded.
        record_btn = AppButton(text="RECORD A TRANSACTION", background_color=hexc("F2C94C"),
                               color=TEXT_DARK, font_size=sp(14), size_hint=(1, None), height=dp(54), radius=40)
        rec = AppButton(text="RECONCILIATION", background_color=hexc("D94B55"),
                        color=(1, 1, 1, 1), font_size=sp(14), size_hint=(1, None), height=dp(54), radius=40)
        jr = AppButton(text="FINANCE JOURNAL", background_color=hexc("E78FB5"),
                       color=TEXT_DARK, font_size=sp(14), size_hint=(1, None), height=dp(54), radius=40)

        def choose_transaction(*_):
            menu = BoxLayout(orientation="vertical", padding=dp(10), spacing=dp(5),
                             size_hint_y=None)
            menu.bind(minimum_height=menu.setter("height"))
            popup = Popup(title="Choose a shop transaction", content=self.scroll_wrap(menu),
                          size_hint=(.88, .82))
            for label, kind in transaction_options.items():
                option = AppButton(text=label, size_hint_y=None, height=dp(44),
                                   background_color=PRIMARY, font_size=sp(12))
                option.bind(on_release=lambda _b, k=kind: (popup.dismiss(), fin_open_form(self, k)))
                menu.add_widget(option)
            close_menu = AppButton(text="CLOSE", size_hint_y=None, height=dp(42), background_color=GREY)
            close_menu.bind(on_release=lambda *_: popup.dismiss())
            menu.add_widget(close_menu)
            popup.open()

        record_btn.bind(on_release=choose_transaction)
        rec.bind(on_release=self.show_reconcile)
        jr.bind(on_release=lambda *_: setattr(self.manager, "current", "fin_journal"))
        finance_actions.add_widget(record_btn)
        finance_actions.add_widget(rec)
        finance_actions.add_widget(jr)
        plan_btn = AppButton(text="EQUIPMENT REPLACEMENT PLAN", background_color=hexc("7FB6E8"),
                             color=TEXT_DARK, font_size=sp(14), size_hint=(1, None), height=dp(54), radius=40)
        plan_btn.bind(on_release=lambda *_: setattr(self.manager, "current", "replacement"))
        finance_actions.add_widget(plan_btn)
        waiting = fin_funding_pending(db)
        if waiting:
            rem = AppButton(text="ADD REMARKS: MONEY ADDED AUTOMATICALLY (" + str(len(waiting)) + ")",
                            background_color=hexc("F2994A"), color=TEXT_DARK, font_size=sp(13),
                            size_hint=(1, None), height=dp(54), radius=40)
            rem.bind(on_release=lambda *_: (_FUNDING_SNOOZED.clear(), fin_prompt_funding_remark(self)))
            finance_actions.add_widget(rem)
            Clock.schedule_once(lambda dt: fin_prompt_funding_remark(self), 0.5)
        layout.add_widget(finance_actions)
        self.set_content(layout)

    def show_detail(self, name, spinner, start, end):
        key = dict(self._detail_keys).get(name)
        spinner.text = "Choose a figure..."
        if not key:
            return
        db = self.manager.app.db
        title, rows = fin_detail(db, key, start, end)
        lines = [title, ("Period: " + (start.isoformat() if start else "start") + " to " + (end - timedelta(days=1)).isoformat())
                 if key not in ("cash", "bank", "mobile_money", "customers", "suppliers", "inventory") else "As at today (all time)", "-" * 40]
        total = 0.0
        import textwrap
        for d, text, a in rows:
            total += a
            lines.append(_lr(short_stamp(d) if d else "opening", num(a), 40))          # date left, amount right
            lines += textwrap.wrap(str(text), 38, initial_indent="  ", subsequent_indent="  ") or []   # full description, never cut
        if not rows:
            lines.append("No records.")
        lines += ["-" * 40, _lr("TOTAL (" + str(len(rows)) + " rows)", num(total), 40)]
        self.show_text_popup(_wrap_report("\n".join(lines), 40), "Details")

    def show_reconcile(self, *_):
        db = self.manager.app.db
        checks = fin_reconcile(db)
        bad = [x for x in checks if not x["ok"]]
        lines = ["RECONCILIATION", "-" * 36,
                 ("ALL CHECKS PASSED" if not bad else f"{len(bad)} DISCREPANCY(IES) FOUND - investigate.\nNothing was adjusted automatically."), ""]
        for x in checks:
            lines.append(("OK   " if x["ok"] else "DIFF ") + x["name"])
            lines.append(f"     expected {num(x['expected'])} | recorded {num(x['actual'])} | diff {num(x['actual'] - x['expected'])}")
            if not x["ok"] and x["note"]:
                lines.append("     " + x["note"])
        self.show_text_popup(_wrap_report("\n".join(lines), 40), "Reconcile")


class Debts(Base):
    """Who owes you and who you owe, in one place: names, balances, payments and older debts."""
    def on_pre_enter(self, *_):
        self.clear_widgets()
        db = self.manager.app.db
        c = fin_compute(db)
        layout = BoxLayout(orientation="vertical", padding=dp(12), spacing=dp(12))
        layout.add_widget(self.top("Customer & Supplier Debts"))
        layout.add_widget(hero_card("Debts", self.shop_name(), "Who owes you, and who you owe."))
        for who, badge, title, total, names, accent in (
                ("customer", "CU", "Customers Owe You", sum(c["customers"].values()), len(c["customers"]), SUCCESS),
                ("supplier", "SU", "You Owe Suppliers", sum(c["suppliers"].values()), len(c["suppliers"]), DANGER)):
            card = role_card(badge, "debts", title, fin_fmt(total) + "  \u2022  " + str(names) + " name" + ("" if names == 1 else "s")
                             + "  \u2022  tap to manage", accent, height=104)
            card.bind(on_release=lambda _w, w=who: Clock.schedule_once(lambda dt: fin_debt_hub(self, w), 0))
            layout.add_widget(card)
        note = Card(orientation="vertical", size_hint_y=None, padding=dp(14), shadow=False)
        note.bind(minimum_height=note.setter("height"))
        note.add_widget(wrap_label("Credit sales (Sale screen, with the customer's name) and credit restocks (Products, with the "
                                   "supplier's name and the amount Paid now) appear here automatically. Open a list to record a "
                                   "payment, or use Record Debt for money that was owed before you started using the app.",
                                   font_size=sp(12), color=TEXT_MUTED))
        layout.add_widget(note)
        self.set_content(layout)


class FinanceJournal(Base):
    """Traceable list of every financial transaction. Mistakes are fixed by reversal, never by deleting history."""

    def on_pre_enter(self, *_):
        self.clear_widgets()
        db = self.manager.app.db
        rows = fin_journal(db)
        layout = BoxLayout(orientation="vertical", padding=dp(8), spacing=dp(4))
        layout.add_widget(self.top("Transaction Journal"))
        layout.add_widget(AppLabel(text=f"{len(rows)} transactions (showing newest {min(len(rows), 150)}). Tap one for details.",
                                   font_size=sp(11), size_hint_y=None, height=dp(30)))
        for r in rows[:150]:
            b = AppButton(text=f"{short_stamp(r['date'])}  {r['category']}  {num(r['amount'])}\n{str(r['ref'])[:30]}  |  {r['status']}  |  {r['method']}",
                          font_size=sp(11), size_hint_y=None, height=dp(52), background_color=(INFO if r["ledger"] else GREY))
            b.bind(on_release=lambda _b, row=r: self.open_row(row))
            layout.add_widget(b)
        self.set_content(layout)

    def open_row(self, r):
        db = self.manager.app.db
        e = r.get("entry")
        lines = [f"ID: {r['id']}", f"Date: {r['date']}", f"Category: {r['category']}", f"Amount: {fin_fmt(r['amount'])}",
                 f"Status: {r['status']}", f"Method: {r['method']}", f"Linked record: {r['ref']}", f"Note: {r['note']}"]
        if e:
            for k in ("party", "kind", "product", "qty", "cost", "principal", "interest", "term", "settles", "restock", "reversal_of", "reversed_by"):
                if e.get(k) not in (None, ""):
                    lines.append(f"{k}: {e[k]}")
        box = BoxLayout(orientation="vertical", padding=dp(8), spacing=dp(6), size_hint_y=None)
        lab = AppLabel(text="\n".join(lines), font_size=sp(12), halign="left", valign="top", size_hint_y=None)
        lab.bind(width=lambda i, w: setattr(i, "text_size", (w, None)))
        lab.bind(texture_size=lambda i, ts: setattr(i, "height", ts[1] + dp(10)))
        box.add_widget(lab)
        popup = Popup(title=self.shop_name() + " - Transaction", content=self.scroll_wrap(box), size_hint=(.94, .8))
        if e and e.get("type") != "opening_balance" and not e.get("reversal_of") and not e.get("reversed_by"):
            reason = AppTextInput(hint_text="Reason for reversing (required)", multiline=False, size_hint_y=None, height=dp(44))
            status = AppLabel(text="", font_size=sp(11), color=DANGER, size_hint_y=None, height=dp(34))
            rev = AppButton(text="REVERSE THIS TRANSACTION", background_color=DANGER, size_hint_y=None, height=dp(46))
            box.add_widget(reason); box.add_widget(status); box.add_widget(rev)

            def do_rev(*_):
                try:
                    if not reason.text.strip():
                        raise ValueError("Give a reason.")
                    fin_reverse(db, r["id"], reason.text.strip())
                    db.save()
                    popup.dismiss()
                    self.on_pre_enter()
                    self.msg("Reversed. The original stays in the journal with its reversal.")
                except Exception as ex:
                    status.text = str(ex)
            rev.bind(on_release=do_rev)
        close = AppButton(text="CLOSE", background_color=GREY, size_hint_y=None, height=dp(42))
        close.bind(on_release=lambda *_: popup.dismiss())
        box.add_widget(close)
        popup.open()
# ====================== FINANCE SCREENS (END) ======================


def _defer_enter(*classes):
    """Open a data-heavy screen at once (so the tapped tile reacts immediately) with a short
    'Loading...' note, then run the screen's ORIGINAL on_pre_enter a moment later. The original
    body is not modified; if it fails, the reason is shown instead of leaving a blank screen."""
    for cls in classes:
        def make(orig):
            def on_pre_enter(self, *a):
                self._build_token = getattr(self, "_build_token", 0) + 1
                token = self._build_token
                self.clear_widgets()
                self.add_widget(AppLabel(text="Loading...", font_size=sp(15), color=TEXT_MUTED, halign="center",
                                         valign="middle", size_hint=(1, None), height=dp(40), pos_hint={"center_y": .5}))

                def build(dt):
                    if token != self._build_token:
                        return
                    try:
                        orig(self, *a)
                    except Exception as exc:
                        self.clear_widgets()
                        self.add_widget(AppLabel(text="Could not open this screen:\n" + str(exc), color=DANGER,
                                                 halign="center", valign="middle"))
                Clock.schedule_once(build, 0.05)
            return on_pre_enter
        cls.on_pre_enter = make(cls.on_pre_enter)


# Screens opened from the admin dashboard that read lots of records. Categories inherits Products.
_defer_enter(LiveToday, Capital, StockPurchases, Products, Reports, Receipts, Expenses, FinanceDashboard, FinanceJournal)


class ShopApp(App):
    title=APP_NAME

    def confirmed_shop_name(self):
        cloud = _cloud_registration()
        if cloud and cloud.get("business_name"):
            return str(cloud.get("business_name"))
        saved = load_saved_license()
        if isinstance(saved, dict):
            payload = saved.get("payload", {})
            if isinstance(payload, dict) and payload.get("business_name"):
                return str(payload.get("business_name"))
        return str(self.db.settings.get("business_name", "My Shop"))

    def build(self):
        self.db=DB()
        self._auto_settle()
        self.admin_session=False
        self.cashier_session=False
        self.license_required=True
        self.license_message="Checking license..."
        self._sync_status = "CHECKING CLOUD"
        self._sync_error = ""
        self._sync_busy = False
        self._sync_pending = False
        self.license_state="none"; self.license_business=""; self.license_days_left=None
        self.license_checking=False; self._last_gate_msg=None
        self.refresh_license_gate()
        # Online licensing: if the phone has not been confirmed with the server recently, hold the app on the
        # licence screen ("Checking...") until the server answers (or fails, then the local licence decides).
        if (not self.license_required) and online_configured() and _sync_license_info():
            last=_parse_iso(_license_state().get("last_online_ok"))
            if (not last) or (_license_now()-last)>timedelta(hours=STARTUP_RECHECK_HOURS):
                self.license_required=True; self.license_checking=True
                self.license_message="Checking your license online...\nPlease wait."
        m=ScreenManager(transition=NoTransition());m.app=self
        for cls,n in [(Home,"home"),(AdminHome,"admin"),(LiveToday,"live_today"),(CashierHome,"cashier"),(Categories,"categories"),(Products,"products"),(Sale,"sale"),(Reports,"reports"),(Expenses,"expenses"),(Settings,"settings"),(Receipts,"receipts"),(Capital,"capital"),(ReplacementPlan,"replacement"),(FinanceDashboard,"finance"),(Debts,"debts"),(FinanceJournal,"fin_journal"),(StockPurchases,"purchases"),(License,"license"),(DeviceManagement,"devices")]:m.add_widget(cls(name=n))
        # FIRST RUN / EXPIRED LICENSE: start on activation, never on the dashboard.
        m.current="home" if not self.license_required else "license"
        def _guard(inst, value):
            # Whatever path is taken, a locked app can only ever show the licence screen.
            if self.license_required and value != "license":
                inst.current = "license"
        m.bind(current=_guard)
        Clock.schedule_interval(lambda dt:self.refresh_license_gate(),30)       # catches expiry while the app is open
        Clock.schedule_interval(lambda dt:self.check_license_online(),1200)     # online check every 20 minutes
        if self.license_checking:
            Clock.schedule_once(lambda dt:self.check_license_online(),0.5)
        else:
            Clock.schedule_once(lambda dt:self.check_license_online(),4)
        try:
            from kivy.core.window import Window as _W
            _W.bind(on_keyboard=self._on_back_key)
        except Exception:pass
        # Weeks / months that end while the app stays open are settled automatically too.
        Clock.schedule_interval(lambda dt:self._auto_settle(),1800)
        if online_configured():
            Clock.schedule_once(lambda dt:self._background_support_sync(),2)
        if _sync_license_info():
            Clock.schedule_once(lambda dt:self.sync_now(),5)
            Clock.schedule_interval(lambda dt:self.sync_now(),SYNC_INTERVAL_SECONDS)
        return m

    def refresh_license_gate(self):
        """Recompute whether the app may be used, and lock / unlock it. Safe to call at any time."""
        if getattr(self, "license_checking", False):
            return "checking"
        state, msg, exp = license_status()
        self.license_state = state
        self.license_days_left = None
        if exp is not None:
            self.license_days_left = (exp - _license_now()).days
        lic = load_saved_license()
        pl = _peek_payload(lic.get("code", "")) if lic else {}
        reg = _cloud_registration() or {}
        self.license_business = str(pl.get("business_name") or reg.get("business_name") or "")
        was_locked = getattr(self, "license_required", True)
        if state == "ok":
            self.license_required = False
            self.license_message = msg
            root = getattr(self, "root", None)
            if was_locked and root is not None and root.current == "license" and not getattr(self, "_in_license_flow", False):
                root.current = "home"
        else:
            self.license_required = True
            self.license_message = msg
            self.admin_session = False
            self.cashier_session = False
            root = getattr(self, "root", None)
            if root is not None:
                if root.current != "license":
                    root.current = "license"
                elif msg != getattr(self, "_last_gate_msg", None):
                    try:
                        scr = root.get_screen("license")
                        if getattr(scr, "mode", "") == "welcome" and hasattr(scr, "mode_status"):
                            scr.mode_status.text = msg
                    except Exception:
                        pass
        self._last_gate_msg = msg
        return state

    def accept_new_license(self, online=False):
        """A new licence / join was just accepted: clear any old withdrawal and re-evaluate."""
        upd = {"revoked": False, "revoked_reason": ""}
        if online:
            upd["last_online_ok"] = _license_now().isoformat()
        license_state_update(**upd)
        self.license_checking = False
        return self.refresh_license_gate()

    def check_license_online(self, on_done=None):
        """Ask the server whether this phone is still allowed. Offline / server trouble never locks the app;
        only an explicit 'withdrawn / not registered' answer does."""
        if getattr(self, "_lic_busy", False) or not online_configured():
            if on_done: on_done("skipped")
            if getattr(self, "license_checking", False):
                self.license_checking = False; self.refresh_license_gate()
            return
        info = _sync_license_info()
        if not info:
            if on_done: on_done("skipped")
            if getattr(self, "license_checking", False):
                self.license_checking = False; self.refresh_license_gate()
            return
        self._lic_busy = True

        def work():
            outcome = "offline"
            try:
                rows = list_business_devices(info)
                mine = next((r for r in rows if isinstance(r, dict) and str(r.get("device_id", "")) == str(info["device_id"])), None)
                status = str((mine or {}).get("status", "")).strip().lower()
                if rows and (mine is None or status in REVOKED_WORDS):
                    license_state_update(revoked=True, revoked_reason="The business or developer has withdrawn access for this phone.")
                    outcome = "revoked"
                else:
                    sd = _SERVER_DATE[0]
                    upd = {"revoked": False, "revoked_reason": "", "last_online_ok": datetime.now(timezone.utc).isoformat()}
                    if sd: upd["max_seen"] = sd.isoformat()       # the server's clock overrides a wrong/rolled-back phone clock
                    license_state_update(**upd)
                    # the server may report the business licence end date: keep the cached copy in step with it
                    for r in rows:
                        if not isinstance(r, dict): continue
                        for k in ("business_expires_at", "license_expires_at"):
                            d = _parse_iso(r.get(k))
                            reg = load_json("cloud_device_registration.json", None)
                            if d and isinstance(reg, dict) and reg.get("business_id") and _parse_iso(reg.get("expires_at")) != d:
                                reg["expires_at"] = d.isoformat(); save_json("cloud_device_registration.json", reg)
                    outcome = "ok"
            except Exception as exc:
                if _classify_sync_error(exc) == "not_registered":
                    license_state_update(revoked=True, revoked_reason="The server no longer recognises this phone for its business.")
                    outcome = "revoked"
                else:
                    outcome = "offline"

            def finish(_dt):
                self._lic_busy = False
                self.license_checking = False
                self.refresh_license_gate()
                if on_done: on_done(outcome)
            Clock.schedule_once(finish, 0)
        threading.Thread(target=work, daemon=True).start()

    def _on_back_key(self, window, key, *args):
        """Android Back (key 27): go back one screen; only the home screen (or the licence gate) exits."""
        if key!=27:return False
        try:
            if getattr(self,"license_required",False):return False
            from kivy.uix.modalview import ModalView
            for _w in list(window.children):             # topmost open popup first
                if isinstance(_w,ModalView):
                    hook=getattr(_w,"_on_back",None)
                    if callable(hook):hook()
                    elif getattr(_w,"auto_dismiss",True):_w.dismiss()
                    return True                          # swallow: never leave the screen under an open popup
            cur=self.root.current
            if cur=="home":return False          # let Kivy close the app
            self.root.get_screen(cur).go_back()
            return True
        except Exception:
            return False

    def sync_summary(self):
        status = str(getattr(self, "_sync_status", "NOT CONFIGURED"))
        if not _sync_license_info():
            return "☁ Cloud sync not configured for this device"
        if status == "LOCAL ONLY":
            return "LOCAL ONLY • One active phone; business data stays on this device"
        if status == "SYNCED":
            stamp = load_json("sync_last_success.json", {})
            return "☁ UP TO DATE • Last sync: " + str(stamp.get("at", "just now"))
        if status == "SYNCING":
            return "☁ SYNCING • Downloading cloud updates and uploading local changes..."
        if status == "PENDING UPLOAD":
            return "☁ PENDING UPLOAD • Local changes are waiting to reach Supabase"
        if status == "CLOUD NOT CONFIGURED":
            return "☁ CLOUD NOT CONFIGURED • Check the Supabase project URL and publishable key"
        if status == "OFFLINE / WAITING TO SYNC":
            return "☁ OFFLINE • Changes remain on this device and will retry"
        if status == "SYNC FAILED":
            return "☁ SYNC FAILED • " + _plain_sync_error(getattr(self, "_sync_error", ""))
        if status == "CLOUD NOT SET UP":
            return "\u2601 LOCAL ONLY \u2022 Cloud sharing is not set up on the server, so this phone works on its own and nothing is uploaded."
        if status == "NOT CONNECTED":
            return ("\u2601 NOT CONNECTED \u2022 This phone is not registered for cloud sharing. A one-phone shop can ignore this; "
                    "with several phones, ask support to register the owner phone.")
        if status == "WAITING FOR ADMIN":
            return "☁ WAITING FOR ADMIN • Products and prices arrive when the admin phone is online"
        if status == "DEVICE REVOKED":
            return "☁ This phone was removed from the business by the administrator. Cloud sharing is off."
        return "☁ " + status

    def refresh_sync_ui(self):
        try:
            screen = self.root.get_screen("home")
            widget = getattr(screen, "sync_indicator", None)
            if widget is not None:
                widget.text = self.sync_summary()
                widget.color = sync_status_color(getattr(self, "_sync_status", ""))
        except Exception:
            pass

    def schedule_sync(self, force=False):
        if not _sync_license_info():
            return
        self._sync_pending=True
        self._sync_status = "CHECKING DEVICES"
        Clock.schedule_once(lambda dt:self.refresh_sync_ui(), 0)
        try:
            Clock.schedule_once(lambda dt:self.sync_now(force=force),1)
        except Exception:
            pass

    def sync_now(self, *_, force=False):
        if getattr(self, "_sync_busy", False) or getattr(self, "license_required", False):
            return
        if not force and time.time() < getattr(self, "_sync_retry_at", 0):
            return                # backing off after a failure, or a one-phone shop checking only every 5 minutes
        if not online_configured():
            self._sync_status = "CLOUD NOT CONFIGURED"
            Clock.schedule_once(lambda dt:self.refresh_sync_ui(), 0)
            return
        info = _sync_license_info()
        if not info:
            return
        self._sync_busy = True
        self._sync_status = "SYNCING"
        Clock.schedule_once(lambda dt:self.refresh_sync_ui(), 0)

        def work():
            try:
                # Check registered devices first. A one-phone business stays local-only:
                # do not assign cloud sync IDs, pull records, or upload any shop data.
                device_rows = list_business_devices(info)
                active_devices = [r for r in device_rows if isinstance(r, dict) and str(r.get("status", "")).lower() == "active"]
                mine = next((r for r in device_rows if isinstance(r, dict) and str(r.get("device_id", "")) == str(info["device_id"])), None)
                if mine is not None and str(mine.get("status", "")).lower() in ("revoked", "blocked", "disabled"):
                    self._sync_pending = False
                    self._sync_status = "DEVICE REVOKED"
                    self._sync_error = ""
                    self._sync_retry_at = time.time() + 600
                    return
                server_role = str((mine or {}).get("device_role") or "").strip().lower()
                if server_role:
                    _remember_device_role(server_role)
                if len(active_devices) <= 1:
                    self._sync_pending = False
                    self._sync_status = "LOCAL ONLY"
                    self._sync_error = ""
                    self._sync_fail_count = 0
                    self._sync_retry_at = time.time() + 300      # one phone: nothing to share, so ask the server only every 5 minutes
                    return
                if mine is None:
                    raise RuntimeError("This phone is not registered for this business (not registered).")
                policy = sync_policy(server_role or device_role())

                def _prepare():
                    if _ensure_sync_ids(self.db, policy["push"]):
                        self.db.save_local_only()
                run_on_kivy_thread(_prepare)

                # Pull all pages first. The server orders by updated_at, dataset, record_id.
                previous_state = load_json("sync_state.json", {})
                if not isinstance(previous_state, dict):
                    previous_state = {}
                cursor = str(previous_state.get("cursor") or "1970-01-01T00:00:00+00:00")
                after_dataset = str(previous_state.get("after_dataset") or "")
                after_record_id = str(previous_state.get("after_record_id") or "")
                pulled = []
                while True:
                    save_json("sync_state.json", {
                        "cursor": cursor,
                        "after_dataset": after_dataset,
                        "after_record_id": after_record_id
                    })
                    page = sync_pull_records(info)
                    if not isinstance(page, list):
                        raise RuntimeError("Unexpected sync response; expected a list.")
                    if not page:
                        break
                    pulled.extend(page)
                    last = page[-1]
                    if not isinstance(last, dict):
                        raise RuntimeError("Invalid sync record.")
                    cursor = str(last.get("updated_at") or "")
                    after_dataset = str(last.get("dataset") or "")
                    after_record_id = str(last.get("record_id") or "")
                    if not cursor or not after_dataset or not after_record_id:
                        raise RuntimeError("Sync response is missing pagination fields.")
                    if len(page) < SYNC_BATCH_SIZE:
                        break

                self._sync_phase = "UPLOADING LOCAL CHANGES"
                def _merge_and_collect():
                    merge_remote_records(self.db, pulled, allowed=policy["pull"])
                    if _ensure_sync_ids(self.db, policy["push"]):
                        self.db.save_local_only()
                    out = _unsent_records(_dataset_records(self.db, policy["push"]))
                    return json.loads(json.dumps(out))      # detached copy: safe to read from this thread
                records = run_on_kivy_thread(_merge_and_collect)
                for i in range(0, len(records), SYNC_BATCH_SIZE):
                    sync_push_records(records[i:i + SYNC_BATCH_SIZE], info)
                _mark_sent(records)

                # Commit local deletion tracking only after every push succeeded.
                pending = load_json("sync_pending_live_ids.json", {})
                known = load_json("sync_known_records.json", {})
                sent = load_json("sync_deleted_sent.json", {})
                if not isinstance(known, dict): known = {}
                if not isinstance(sent, dict): sent = {}
                for dataset in policy["push"]:
                    live = set(pending.get(dataset, [])) if isinstance(pending, dict) else set()
                    old = set(known.get(dataset, [])) if isinstance(known.get(dataset, []), list) else set()
                    removed = old - live
                    sentset = set(sent.get(dataset, [])) if isinstance(sent.get(dataset, []), list) else set()
                    sent[dataset] = sorted(sentset | removed)
                    known[dataset] = sorted(live | sentset)
                save_json("sync_known_records.json", known)
                save_json("sync_deleted_sent.json", sent)
                save_json("sync_state.json", {
                    "cursor": cursor,
                    "after_dataset": after_dataset,
                    "after_record_id": after_record_id
                })
                self._sync_pending = False
                self._sync_status = "SYNCED"
                self._sync_fail_count = 0
                self._sync_retry_at = 0
                if policy is sync_policy("employee") and not self.db.products:
                    self._sync_status = "WAITING FOR ADMIN"    # the admin phone has not shared the shop yet
                    Clock.schedule_once(lambda dt: self.fast_sync(300), 0)   # look again every 10 s until it arrives
                self._sync_error = ""
                save_json("sync_last_success.json", {"at": datetime.now().astimezone().strftime("%Y-%m-%d %H:%M:%S")})
            except Exception as e:
                kind = _classify_sync_error(e)
                self._sync_fail_count = getattr(self, "_sync_fail_count", 0) + 1
                self._sync_retry_at = time.time() + _sync_wait_seconds(kind, self._sync_fail_count)
                self._sync_status = {"offline": "OFFLINE / WAITING TO SYNC", "not_installed": "CLOUD NOT SET UP",
                                     "not_registered": "NOT CONNECTED"}.get(kind, "SYNC FAILED")
                self._sync_error = str(e)
            finally:
                Clock.schedule_once(lambda dt: setattr(self, "_sync_busy", False), 0)
                Clock.schedule_once(lambda dt: self.refresh_sync_ui(), 0)
                try:
                    self._report_sync_event()
                except Exception:
                    pass

        try:
            threading.Thread(target=work, daemon=True).start()
        except Exception:
            self._sync_busy = False

    def _report_sync_event(self):
        """Best-effort anonymous status for Developer Control's Live Monitor.
        Throttled (5 min unless the status changes) and switched off for the session
        if the optional server function is not installed. Failure never affects the app."""
        if getattr(self, "_report_disabled", False) or not online_configured():
            return
        info = _sync_license_info()
        if not info:
            return
        status = str(getattr(self, "_sync_status", ""))
        kind = {"SYNCED": ("sync_ok", "ok"), "LOCAL ONLY": ("heartbeat", "ok"),
                "OFFLINE / WAITING TO SYNC": ("sync_offline", "offline"),
                "SYNC FAILED": ("sync_failed", "failed")}.get(status)
        if not kind:
            return
        err = "" if kind[1] == "ok" else _error_class(getattr(self, "_sync_error", ""))
        key = status + "|" + err
        now = time.time()
        last = getattr(self, "_last_report", None)
        if last and last[0] == key and now - last[1] < 300:
            return
        self._last_report = (key, now)
        try:
            report_device_event(info, kind[0], kind[1], err)
        except Exception as e:
            low = str(e).lower()
            if "404" in low or "pgrst202" in low or "could not find the function" in low:
                self._report_disabled = True

    def fast_sync(self, seconds=600):
        """After a joining code is generated, check for the new device every 10 s (then back to normal)."""
        self._fast_sync_until = time.time() + seconds
        if getattr(self, "_fast_sync_event", None):
            return

        def tick(dt):
            if time.time() > getattr(self, "_fast_sync_until", 0):
                self._fast_sync_event = None
                return False
            self.sync_now(force=True)
        self._fast_sync_event = Clock.schedule_interval(tick, 10)

    def _auto_settle(self):
        try:self.db.settle_periods()
        except Exception:pass
    def _background_support_sync(self):
        def work():
            try: fetch_support_online()
            except Exception: pass
        threading.Thread(target=work,daemon=True).start()
    def on_resume(self):
        self._auto_settle()
        self.refresh_license_gate()
        self.check_license_online()
        self.sync_now()
    def on_pause(self):
        self.db.save();return True
    def on_stop(self):self.db.save()
if __name__=="__main__":ShopApp().run()
