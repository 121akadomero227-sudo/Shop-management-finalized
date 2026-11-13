[app]

# ---- Identity ----
title = Shop Management
# Choose package.name / package.domain ONCE. Changing them later makes Android treat the app as a
# different app, so shops could not update over the old install.
package.name = shopmanagement
package.domain = org.shopmanagement
version = 2.5.0

# ---- Source ----
source.dir = .
source.include_exts = py,png,jpg,kv,atlas,json,ttf
source.exclude_dirs = bin,.buildozer,venv,tests

# ---- Requirements ----
# openssl / sqlite are pulled in automatically by python3. certifi gives HTTPS a CA bundle.
requirements = python3,kivy==2.3.1,pyjnius,android,certifi

# ---- Launch screen (replaces the blank screen with loading text) ----
presplash.filename = %(source.dir)s/presplash.png
android.presplash_color = #111111

# ---- Icons ----
icon.filename = %(source.dir)s/icon.png
icon.adaptive_foreground.filename = %(source.dir)s/icon_foreground.png
icon.adaptive_background.filename = %(source.dir)s/icon_background.png

# ---- Display ----
orientation = portrait
fullscreen = 0

# ---- Android ----
# The app only needs the internet (licence, support, cloud sync). Receipts are saved through
# MediaStore / app storage, dialling and sharing use intents, so no storage/phone permissions.
android.permissions = INTERNET
android.api = 36
android.minapi = 24
android.ndk = 28c
android.archs = arm64-v8a, armeabi-v7a
android.accept_sdk_license = True
android.release_artifact = apk
android.debug_artifact = apk
android.allow_backup = True

# ---- python-for-android ----
p4a.branch = develop

[buildozer]
log_level = 2
warn_on_root = 1
