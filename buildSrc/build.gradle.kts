/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import java.util.*

plugins {
    `kotlin-dsl`
}

val cacheRedirectorEnabled = System.getenv("CACHE_REDIRECTOR")?.toBoolean() == true
val buildSnapshotTrain = properties["build_snapshot_train"]?.toString()?.toBoolean() == true

repositories {
    mavenCentral()
    if (cacheRedirectorEnabled) {
        maven("https://cache-redirector.jetbrains.com/plugins.gradle.org/m2")
    } else {
        maven("https://plugins.gradle.org/m2")
    }
    maven("https://maven.pkg.jetbrains.space/kotlin/p/kotlin/dev")

    if (buildSnapshotTrain) {
        mavenLocal()
    }
}

kotlinDslPluginOptions {
    experimentalWarning.set(false)
}

val props = Properties().apply {
    file("../gradle.properties").inputStream().use { load(it) }
}

fun version(target: String): String {
    // Intercept reading from properties file
    if (target == "kotlin") {
        val snapshotVersion = properties["kotlin_snapshot_version"]
        if (snapshotVersion != null) return snapshotVersion.toString()
    }
    return props.getProperty("${target}_version")
}

dependencies {
    implementation(kotlin("gradle-plugin", version("kotlin")))
    implementation("org.jetbrains.dokka:dokka-gradle-plugin:${version("dokka")}")
    implementation("org.jetbrains.dokka:dokka-core:${version("dokka")}")
    implementation("ru.vyarus:gradle-animalsniffer-plugin:1.5.3") // Android API check
}
