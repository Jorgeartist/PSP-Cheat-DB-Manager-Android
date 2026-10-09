plugins {
    id("com.android.application")
    id("org.jetbrains.kotlin.android")
}

android {
    namespace = "com.pspcheatdb.manager"
    compileSdk = 35
    defaultConfig {
        applicationId = "com.pspcheatdb.manager"
        minSdk = 23
        targetSdk = 35
        versionCode = 26
        versionName = "0.7.11"
    }
    compileOptions {
        sourceCompatibility = JavaVersion.VERSION_1_8
        targetCompatibility = JavaVersion.VERSION_1_8
    }
    kotlinOptions { jvmTarget = "1.8" }
}
