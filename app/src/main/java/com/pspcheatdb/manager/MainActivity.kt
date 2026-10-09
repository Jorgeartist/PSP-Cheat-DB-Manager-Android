package com.pspcheatdb.manager

import android.app.Activity
import android.app.AlertDialog
import android.content.Intent
import android.content.pm.ActivityInfo
import android.database.ContentObserver
import android.graphics.Bitmap
import android.graphics.BitmapFactory
import android.graphics.Color
import android.graphics.Typeface
import android.graphics.drawable.GradientDrawable
import android.net.Uri
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.provider.DocumentsContract
import android.text.Editable
import android.text.TextWatcher
import android.view.Gravity
import android.view.KeyEvent
import android.view.View
import android.view.ViewGroup
import android.widget.*
import android.text.TextUtils
import android.text.InputType
import android.util.Base64
import org.json.JSONArray
import org.json.JSONObject
import java.io.BufferedReader
import java.io.InputStreamReader
import java.net.HttpURLConnection
import java.net.URL
import java.net.URLDecoder
import java.net.URLEncoder
import java.io.File
import java.security.MessageDigest
import java.security.KeyStore
import javax.crypto.Cipher
import javax.crypto.KeyGenerator
import javax.crypto.SecretKey
import javax.crypto.spec.GCMParameterSpec
import android.security.keystore.KeyGenParameterSpec
import android.security.keystore.KeyProperties
import java.util.Locale
import java.util.concurrent.Executors
import java.util.concurrent.CompletionService
import java.util.concurrent.Callable
import java.util.concurrent.ExecutorCompletionService
import java.util.concurrent.Future
import java.util.concurrent.TimeUnit
import java.util.concurrent.ConcurrentHashMap
import java.util.zip.ZipInputStream

class MainActivity : Activity() {
    private val db = linkedMapOf<String, Game>()
    private val worker = Executors.newSingleThreadExecutor()
    private val coverWorker = Executors.newFixedThreadPool(2)
    private val coverProbeWorkers = Executors.newFixedThreadPool(6)
    private val folderScanWorker = Executors.newSingleThreadExecutor()
    private var pendingFolderScanAfterPick = false
    private var folderScanDialogText: TextView? = null
    private var gameSortMode = "Recently added"
    private var cheatSortMode = "Name A–Z"
    private var controllerStyle = "Switch"
    private var coverLayout = "Compact Details"
    private var focusedGameRowId = ""
    private var libraryMode = "games"
    private var tutorialFolderLabel: TextView? = null
    private var tutorialImportChoice = "single"
    private var progressDialog: AlertDialog? = null
    private var progressBar: ProgressBar? = null
    private var progressText: TextView? = null
    private var notificationPopup: PopupWindow? = null
    private val notificationHandler = Handler(Looper.getMainLooper())
    private val visibleCheatKeys = mutableListOf<Pair<String, Int>>()
    private lateinit var selectVisibleButton: Button
    private lateinit var quickFavoriteButton: Button
    private val activeCoverSearches = ConcurrentHashMap.newKeySet<String>()
    private val recentCoverViews = mutableMapOf<String, ImageView>()
    private val recentCoverStatusViews = mutableMapOf<String, TextView>()
    private lateinit var root: LinearLayout
    private lateinit var gameId: EditText
    private lateinit var title: AutoCompleteTextView
    private lateinit var query: EditText
    private lateinit var results: LinearLayout
    private lateinit var status: TextView
    private lateinit var count: TextView
    private lateinit var themeButton: Button
    private lateinit var selectedGameFile: TextView
    private lateinit var selectedCountLabel: TextView
    private lateinit var coverImageView: ImageView
    private lateinit var coverOverlayView: TextView
    private lateinit var mainCoverImageView: ImageView
    private var theme = "Ghost Protocol"
    private var filter = "All"
    private var colors = palette(theme)
    private val selected = linkedSetOf<Pair<String, Int>>()
    private val titleCatalog = mutableListOf<GameTitle>()
    private lateinit var catalogStatus: TextView
    private lateinit var advancedPanel: LinearLayout
    private lateinit var advancedToggle: Button
    private lateinit var exportFolderLabel: TextView
    private var pendingExport: Pair<String, String>? = null
    private var currentScreen = "search"
    private var currentGameId = ""
    private var settingsTab = "General"
    private var settingsOriginScreen = "search"
    private var customSourceUrl = ""
    private var pendingTourDialog: AlertDialog? = null
    private val autoSearchHandler = Handler(Looper.getMainLooper())
    private var autoSearch: Runnable? = null
    private var suppressAutoSearch = false
    private val installedIniStats = linkedMapOf<String, InstalledIniStats>()
    private var installedIniSummary = "PPSSPP INI files have not been scanned yet."
    private var installedIniScanComplete = false
    private var installedIniScanInProgress = false
    private var installedIniFingerprint = ""
    private var installedIniFingerprintInitialized = false
    private var iniMonitorActive = false
    private var iniFingerprintCheckInFlight = false
    private var iniContentObserver: ContentObserver? = null
    private var iniObservedChildrenUri: Uri? = null
    private var iniRescanRunnable: Runnable? = null
    private var iniPollRunnable: Runnable? = null
    private val iniMonitorHandler = Handler(Looper.getMainLooper())

    private data class InstalledIniStats(var files: Int = 0, var mods: Int = 0, var enabled: Int = 0)
    private data class IniFileRef(val documentId: String, val name: String, val size: Long, val lastModified: Long)

    data class Cheat(val name: String, val codes: List<Pair<String, String>>, val source: String)
    data class Game(val id: String, var title: String, val cheats: MutableList<Cheat> = mutableListOf())
    data class GameTitle(val title: String, val id: String, val region: String) { override fun toString() = "$title  —  $region  —  $id" }

    private fun countryName(region: String): String = when (region.trim().lowercase(Locale.ROOT)) {
        "usa", "united states" -> "United States"
        "europe", "eu" -> "Europe"
        "japan", "jp" -> "Japan"
        "asia" -> "Asia"
        "korea", "south korea" -> "South Korea"
        "australia", "au" -> "Australia"
        "world", "worldwide" -> "World"
        else -> region.ifBlank { "Region unknown" }
    }

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        requestedOrientation = ActivityInfo.SCREEN_ORIENTATION_SENSOR_LANDSCAPE
        customSourceUrl = getSharedPreferences("prefs", 0).getString("custom_source_url", "") ?: ""
        val prefs = getSharedPreferences("prefs", 0)
        gameSortMode = prefs.getString("game_sort", "Recently added") ?: "Recently added"
        cheatSortMode = prefs.getString("cheat_sort", "Name A–Z") ?: "Name A–Z"
        controllerStyle = normalizeControllerStyle(prefs.getString("controller_style", "Switch") ?: "Switch")
        coverLayout = prefs.getString("cover_layout", "Compact Details") ?: "Compact Details"
        loadDb()
        buildUi()
        showWelcomeIfNeeded()
        loadTitleCatalog()
    }

    override fun onResume() {
        super.onResume()
        startPpssppIniMonitoring()
    }

    override fun onPause() {
        stopPpssppIniMonitoring()
        super.onPause()
    }

    private fun palette(name: String): IntArray = when (name) {
        "Matrix" -> intArrayOf(Color.rgb(5,8,5), Color.rgb(10,18,10), Color.rgb(225,255,228), Color.rgb(7,15,7), Color.rgb(57,255,20))
        "Ghost Protocol" -> intArrayOf(Color.rgb(5,15,27), Color.rgb(10,30,49), Color.rgb(224,248,255), Color.rgb(7,23,39), Color.rgb(35,218,255))
        "Vice City" -> intArrayOf(Color.rgb(20,8,29), Color.rgb(39,15,55), Color.rgb(255,237,251), Color.rgb(27,10,41), Color.rgb(255,55,174))
        "Kratos" -> intArrayOf(Color.rgb(16,11,14), Color.rgb(35,24,30), Color.rgb(247,233,237), Color.rgb(25,16,21), Color.rgb(220,35,63))
        "Midnight Club" -> intArrayOf(Color.rgb(5,13,26), Color.rgb(15,28,48), Color.rgb(255,245,220), Color.rgb(8,19,37), Color.rgb(255,181,46))
        "Wipeout" -> intArrayOf(Color.rgb(241,245,248), Color.rgb(224,232,237), Color.rgb(18,27,35), Color.rgb(250,252,253), Color.rgb(255,103,31))
        "Liberty City" -> intArrayOf(Color.rgb(21,24,28), Color.rgb(37,43,49), Color.rgb(237,240,243), Color.rgb(27,32,37), Color.rgb(157,169,181))
        "Patapon" -> intArrayOf(Color.rgb(8,8,7), Color.rgb(23,20,10), Color.rgb(255,247,211), Color.rgb(13,12,9), Color.rgb(255,213,46))
        "Neon Genesis" -> intArrayOf(Color.rgb(15,8,24), Color.rgb(31,17,46), Color.rgb(245,239,255), Color.rgb(21,11,34), Color.rgb(178,255,0))
        "Arctic Camo" -> intArrayOf(Color.rgb(218,234,241), Color.rgb(240,248,251), Color.rgb(20,43,55), Color.rgb(228,241,246), Color.rgb(44,165,213))
        "Stealth Ops" -> intArrayOf(Color.rgb(17,21,12), Color.rgb(38,44,25), Color.rgb(237,242,218), Color.rgb(25,31,17), Color.rgb(255,157,48))
        "Afterburner" -> intArrayOf(Color.rgb(22,8,10), Color.rgb(44,16,22), Color.rgb(255,235,224), Color.rgb(32,11,15), Color.rgb(231,103,42))
        else -> intArrayOf(Color.rgb(5,8,5), Color.rgb(10,18,10), Color.rgb(225,255,228), Color.rgb(7,15,7), Color.rgb(57,255,20))
    }

    private fun themeIcon(name: String): String = when (name) {
        "Matrix" -> "⌘"; "Ghost Protocol" -> "🛡️"; "Vice City" -> "🌴"; "Kratos" -> "⚔️"
        "Midnight Club" -> "🏁"; "Wipeout" -> "⚡"; "Liberty City" -> "🏙️"; "Patapon" -> "🥁"
        "Neon Genesis" -> "🤖"; "Arctic Camo" -> "❄️"; "Stealth Ops" -> "🎯"; else -> "🔥"
    }
    private fun themeVibe(name: String): String = when (name) {
        "Matrix" -> "Neon green / black · digital terminal"
        "Ghost Protocol" -> "Cyan / deep navy · futuristic PSP"
        "Vice City" -> "Hot pink / purple · retro nightlife"
        "Kratos" -> "Crimson / charcoal · mythic combat"
        "Midnight Club" -> "Amber / midnight blue · street racing"
        "Wipeout" -> "White / orange · futuristic racing"
        "Liberty City" -> "Steel grey / graphite · urban industrial"
        "Patapon" -> "Golden yellow / black · bold arcade"
        "Neon Genesis" -> "Acid green / violet · anime mecha"
        "Arctic Camo" -> "Ice blue / frost white · cool tactical"
        "Stealth Ops" -> "Orange / military olive · tactical HUD"
        else -> "Burnt orange / dark burgundy · intense arcade"
    }
    private val themeNames = arrayOf("Matrix", "Ghost Protocol", "Vice City", "Kratos", "Midnight Club", "Wipeout", "Liberty City", "Patapon", "Neon Genesis", "Arctic Camo", "Stealth Ops", "Afterburner")
    private fun migrateTheme(name: String): String = when (name) {
        "PSP Blue", "Teal", "Matrix", "MTRX", "Black (Base)" -> "Ghost Protocol"
        "PSP Gold" -> "Midnight Club"
        "White" -> "Wipeout"
        "Cool Grey" -> "Liberty City"
        "GOWGHST" -> "Kratos"
        "Purple", "Kawaii" -> "Vice City"
        "JAKDAX" -> "Patapon"
        else -> name.takeIf { it in themeNames } ?: "Ghost Protocol"
    }

    private fun buildUi() {
        colors = palette(theme)
        val compact = compactLandscape()
        root = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(8, 7, 8, 6); setBackgroundColor(colors[0]) }
        val header = LinearLayout(this).apply { gravity = Gravity.CENTER_VERTICAL; orientation = LinearLayout.HORIZONTAL; setPadding(10, 5, 10, 5); background = surface(colors[3], colors[4]) }
        header.addView(TextView(this).apply { text = "PSP CHEAT DB MANAGER"; textSize = if (compact) 18f else 23f; setTextColor(colors[2]); typeface = Typeface.create("sans-serif-condensed", Typeface.BOLD); setPadding(8, 0, 12, 0) }, LinearLayout.LayoutParams(0, if (compact) 44 else 58, 1f))
        count = TextView(this).apply { setTextColor(colors[2]); textSize = 14f; gravity = Gravity.RIGHT or Gravity.CENTER_VERTICAL; typeface = Typeface.create("sans-serif-condensed", Typeface.NORMAL); setPadding(8, 0, 8, 0) }; header.addView(count, LinearLayout.LayoutParams(0, -1, 1f))
        header.addView(TextView(this).apply { text = "v0.7.11"; setTextColor(colors[2]); textSize = 13f; gravity = Gravity.CENTER; setPadding(6, 0, 6, 0) })
        root.addView(header, LinearLayout.LayoutParams(-1, if (compact) 50 else 66))
        val workArea = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; setPadding(0, 5, 0, 5) }
        val left = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(10, 10, 10, 8); background = surface(colors[1], colors[4]) }
        val gameCard = FrameLayout(this).apply { background = GradientDrawable(GradientDrawable.Orientation.TL_BR, intArrayOf(colors[3], colors[1], colors[3])).apply { cornerRadius = dp(7).toFloat(); setStroke(dp(1), this@MainActivity.colors[4]) } }
        mainCoverImageView = ImageView(this).apply { scaleType = ImageView.ScaleType.CENTER_CROP; setBackgroundColor(colors[3]) }
        gameCard.addView(mainCoverImageView, FrameLayout.LayoutParams(-1, -1))
        selectedGameFile = TextView(this).apply { text = "ＰＳＰ\n\nTAP TO SEARCH COVER ART\n\nLOAD A GAME\nISO / PBP / CHD"; textSize = if (compact) 14f else 18f; setTextColor(colors[4]); gravity = Gravity.CENTER; typeface = Typeface.create("sans-serif-condensed", Typeface.BOLD); background = GradientDrawable(GradientDrawable.Orientation.BOTTOM_TOP, intArrayOf(0xAA000000.toInt(), Color.TRANSPARENT)); setPadding(8, 8, 8, 8) }
        gameCard.addView(selectedGameFile, FrameLayout.LayoutParams(-1, -1))
        gameCard.setOnClickListener { searchCoverArtForSelection(mainCoverImageView) }
        left.addView(gameCard, LinearLayout.LayoutParams(-1, 0, 1f))
        left.addView(button("▱  ADD PSP GAME") { showGameImportOptions() }, LinearLayout.LayoutParams(-1, if (compact) 42 else 48))
        left.addView(label("SEARCH BY GAME ID / TITLE").apply { textSize = if (compact) 11f else 14f })
        gameId = edit("Game ID · UCUS98744"); left.addView(gameId)
        title = AutoCompleteTextView(this).apply { hint = "Game title or ID"; threshold = 1; setHintTextColor(colors[4]); setTextColor(colors[2]); textSize = if (compact) 13f else 15f; setSingleLine(true); setBackgroundColor(colors[3]); setPadding(12, 8, 8, 8) }
        left.addView(title)
        left.addView(button("⌕  SEARCH / OPEN GAME") { searchCurrentGame() }, LinearLayout.LayoutParams(-1, if (compact) 38 else 48))
        quickFavoriteButton = button(if (isFavorite(activeGameId())) "★  FAVORITED" else "☆  QUICK FAVORITE") { toggleQuickFavorite() }
        left.addView(quickFavoriteButton, LinearLayout.LayoutParams(-1, if (compact) 38 else 48))
        workArea.addView(left, LinearLayout.LayoutParams(0, -1, .28f))

        val center = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(12, 10, 12, 8); background = surface(colors[1], colors[4]) }
        val prompt = TextView(this).apply { text = "GAMES   /   CHEAT LIBRARY"; textSize = if (compact) 15f else 18f; setTextColor(colors[2]); typeface = Typeface.create("sans-serif-condensed", Typeface.BOLD); setPadding(3, 3, 3, 5) }; center.addView(prompt)
        catalogStatus = label("Loading PSP game titles…"); center.addView(catalogStatus)
        val homeContent = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(4, 8, 4, 8) }
        homeContent.addView(TextView(this).apply { text = "RECENTLY OPENED GAMES"; textSize = if (compact) 15f else 18f; setTextColor(colors[2]); typeface = Typeface.create("sans-serif-condensed", Typeface.BOLD); setPadding(8, 4, 8, 8) })
        val recentIds = readRecentGameIds()
        if (recentIds.isEmpty()) {
            homeContent.addView(TextView(this).apply { text = "Games you open will appear here. Choose a game file or search by title to get started."; textSize = if (compact) 14f else 16f; setTextColor(colors[4]); gravity = Gravity.CENTER; setPadding(20, 12, 20, 12) }, LinearLayout.LayoutParams(-1, 0, 1f))
        } else {
            recentIds.take(6).forEach { id ->
                val meta = titleCatalog.firstOrNull { it.id == id }
                val gameName = meta?.title ?: db[id]?.title?.ifBlank { null } ?: id
                val recentCard = LinearLayout(this).apply {
                    orientation = LinearLayout.VERTICAL; gravity = Gravity.CENTER_VERTICAL
                    setPadding(dp(10), dp(7), dp(10), dp(7)); setMinimumHeight(dp(56)); background = surface(colors[1], colors[4]); isClickable = true; isFocusable = true
                    setOnClickListener { openModsScreen(id) }
                }
                recentCard.addView(TextView(this).apply {
                    text = "▶  $gameName"; textSize = if (compact) 13f else 15f; setTextColor(colors[2]); typeface = Typeface.create("sans-serif-condensed", Typeface.NORMAL)
                    maxLines = 2; ellipsize = TextUtils.TruncateAt.END; includeFontPadding = true
                }, LinearLayout.LayoutParams(-1, -2))
                recentCard.addView(TextView(this).apply {
                    text = "${meta?.region ?: "PSP game"}  ·  $id"; textSize = if (compact) 11f else 12f; setTextColor(colors[4]); typeface = Typeface.create("sans-serif-condensed", Typeface.NORMAL)
                    maxLines = 1; ellipsize = TextUtils.TruncateAt.END; includeFontPadding = true
                }, LinearLayout.LayoutParams(-1, -2))
                homeContent.addView(recentCard, LinearLayout.LayoutParams(-1, -2).apply { bottomMargin = dp(5) })
            }
        }
        val homeScroll = ScrollView(this).apply { addView(homeContent) }
        center.addView(homeScroll, LinearLayout.LayoutParams(-1, 0, 1f))
        advancedToggle = button("DATABASE & EXPORT OPTIONS   ▾") { toggleAdvanced() }; center.addView(advancedToggle)
        advancedPanel = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(6, 4, 6, 4); visibility = View.GONE }
        advancedPanel.addView(button("Import or merge cheat database (.db, .ini, .txt, .zip)") { openDocument(REQ_IMPORT) })
        exportFolderLabel = label(exportFolderText()); advancedPanel.addView(exportFolderLabel)
        advancedPanel.addView(button("Choose PPSSPP PSP/Cheats folder") { chooseExportFolder() })
        query = edit("Filter available cheats by name"); advancedPanel.addView(query)
        val filters = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL }
        listOf("All", "60 FPS", "3:2", "Ultrawide").forEach { f -> filters.addView(button(f) { filter = f; renderResults() }, LinearLayout.LayoutParams(0, -2, 1f)) }
        advancedPanel.addView(filters)
        advancedPanel.addView(button("Export selected as GAMEID.ini") { exportSelected() })
        advancedPanel.addView(button("Export all as GAMEID.ini") { exportGame() })
        center.addView(advancedPanel)
        status = label("Ready. Imported cheats are reference text and are not verified."); center.addView(status)
        workArea.addView(center, LinearLayout.LayoutParams(0, -1, .72f))
        val rail = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(3, 2, 3, 2); background = surface(colors[1], colors[4]) }
        if (compact) addCompactRailActions(rail) else addFullRailActions(rail)
        workArea.addView(rail, LinearLayout.LayoutParams(dp(if (compact) 52 else 76), -1))
        root.addView(workArea, LinearLayout.LayoutParams(-1, 0, 1f))
        root.addView(controllerFooter("home"))
        title.setOnItemClickListener { _, _, position, _ ->
            val item = title.adapter?.getItem(position) as? GameTitle
            if (item != null) { gameId.setText(item.id); title.setText(item.title, false); title.setSelection(title.text.length); title.dismissDropDown(); selectedGameFile.text = "${item.title}\n${item.id} · ${countryName(item.region)}\nTAP TO SEARCH COVER ART"; openModsScreen(item.id) }
        }
        gameId.addTextChangedListener(object : TextWatcher {
            override fun beforeTextChanged(s: CharSequence?, start: Int, count: Int, after: Int) {}
            override fun onTextChanged(s: CharSequence?, start: Int, before: Int, count: Int) {
                autoSearch?.let { autoSearchHandler.removeCallbacks(it) }
                val entered = s?.toString()?.uppercase()?.replace(Regex("[-_ ]"), "")?.trim().orEmpty()
                if (!suppressAutoSearch && currentScreen == "search" && entered.matches(Regex("[A-Z]{4}\\d{5}"))) {
                    autoSearch = Runnable { if (gameId.text.toString().uppercase().replace(Regex("[-_ ]"), "").trim() == entered) openModsScreen(entered) }
                    autoSearchHandler.postDelayed(autoSearch!!, 700)
                }
            }
            override fun afterTextChanged(s: Editable?) {}
        })
        results = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL }
        setContentView(root); updateCount()
    }

    private fun toggleAdvanced() {
        advancedPanel.visibility = if (advancedPanel.visibility == View.VISIBLE) View.GONE else View.VISIBLE
        advancedToggle.text = if (advancedPanel.visibility == View.VISIBLE) "HIDE DATABASE & EXPORT OPTIONS   ▴" else "DATABASE & EXPORT OPTIONS   ▾"
    }

    private fun addCompactRailActions(rail: LinearLayout) {
        val actions: List<Triple<String, String, () -> Unit>> = listOf(
            Triple("⌂", "Home · last opened game", { returnToSearch() }),
            Triple("▥", "Games · full library", { openGamesScreen() }),
            Triple("★", "Favorites", { openCollectionScreen("favorites") }),
            Triple("◷", "Recent games", { openCollectionScreen("recent") }),
            Triple("⚙", "Settings", { showSettingsScreen() })
        )
        actions.forEach { (icon, description, action) -> rail.addView(railButton(icon, description, action, true), LinearLayout.LayoutParams(-1, 0, 1f)) }
    }

    private fun addFullRailActions(rail: LinearLayout) {
        val actions: List<Triple<String, String, () -> Unit>> = listOf(
            Triple("⌂", "Home · last opened game", { returnToSearch() }),
            Triple("▥", "Games · full library", { openGamesScreen() }),
            Triple("▤", "Database · import cheats", { openDocument(REQ_IMPORT) }),
            Triple("▧", "Export", { showExportActions() }),
            Triple("★", "Favorites", { openCollectionScreen("favorites") }),
            Triple("◷", "Recent games", { openCollectionScreen("recent") }),
            Triple("⚙", "Settings", { showSettingsScreen() })
        )
        actions.forEach { (icon, description, action) -> rail.addView(railButton(icon, description, action, false), LinearLayout.LayoutParams(-1, 0, 1f)) }
    }

    private fun railButton(icon: String, description: String, action: () -> Unit, compact: Boolean): Button =
        button(icon, action).apply {
            contentDescription = description
            textSize = if (compact) 25f else 22f
            typeface = Typeface.create("sans-serif", Typeface.NORMAL)
            gravity = Gravity.CENTER
        }

    private fun showSettingsScreen() {
        if (currentScreen != "settings") settingsOriginScreen = currentScreen
        currentScreen = "settings"
        val page = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(10, 8, 10, 8); setBackgroundColor(colors[0]) }
        val head = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL; background = surface(colors[3], colors[4]); setPadding(8, 5, 8, 5) }
        head.addView(button("‹ BACK") {
            when {
                settingsOriginScreen == "mods" && currentGameId.isNotBlank() -> openModsScreen(currentGameId)
                settingsOriginScreen in setOf("games", "recent", "favorites") -> openCollectionScreen(settingsOriginScreen)
                else -> returnToSearch()
            }
        })
        head.addView(TextView(this).apply { text = "SETTINGS"; textSize = 21f; setTextColor(colors[2]); typeface = Typeface.create("sans-serif-condensed", Typeface.BOLD); gravity = Gravity.CENTER }, LinearLayout.LayoutParams(0, 50, 1f))
        page.addView(head)
        val tabs = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; setPadding(0, 7, 0, 6) }
        listOf("General", "Themes", "Sources", "Cover Art", "Controller").forEach { tab ->
            tabs.addView(button(if (settingsTab == tab) "◆  ${tab.uppercase()}" else tab.uppercase()) { settingsTab = tab; showSettingsScreen() }, LinearLayout.LayoutParams(0, 46, 1f))
        }
        page.addView(tabs)
        val content = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(14, 12, 14, 12); background = surface(colors[1], colors[4]) }
        when (settingsTab) {
            "Themes" -> buildThemeSettings(content)
            "Sources" -> buildSourcesSettings(content)
            "Cover Art" -> buildCoverArtSettings(content)
            "Controller" -> buildControllerSettings(content)
            else -> {
                content.addView(label("GAME LIBRARY FOLDER"))
                content.addView(label(gameFolderText()))
                content.addView(button("Choose PSP ISO / PBP / CHD folder") { chooseGameFolder() })
                content.addView(button("Scan remembered game folder now") { confirmFullFolderScan() })
                content.addView(label("EXPORT LOCATION"))
                content.addView(label(exportFolderText()))
                content.addView(button("Choose PPSSPP PSP/Cheats folder") { chooseExportFolder() })
                content.addView(button("Scan installed game INI files") { scanPpssppCheatFolder() })
                content.addView(label(installedIniSummary))
                content.addView(label("Enabled mods are marked _C1 in the INI. _C0 entries are present but disabled."))
                content.addView(label("For the smoothest setup, install PPSSPP first so you can select its PSP/Cheats folder above."))
                content.addView(button("Reset app to fresh-install defaults…") { resetAppToFreshInstall() })
            }
        }
        val scroller = ScrollView(this); scroller.addView(content)
        page.addView(scroller, LinearLayout.LayoutParams(-1, 0, 1f))
        status = label("Settings are saved on this device.").apply { setTextColor(colors[4]) }; page.addView(status)
        page.addView(TextView(this).apply { text = "PSP CHEAT DB MANAGER  ·  v0.7.11"; setTextColor(colors[4]); gravity = Gravity.CENTER; textSize = 12f; setPadding(5, 6, 5, 3) })
        page.addView(controllerFooter("settings"))
        setContentView(page)
    }

    private fun buildThemeSettings(container: LinearLayout) {
        container.addView(label("APP APPEARANCE"))
        container.addView(label("Choose a preset tile to preview and apply its color palette."))
        themeNames.toList().chunked(2).forEachIndexed { rowIndex, pair ->
            val row = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL }
            pair.forEachIndexed { columnIndex, name ->
                val swatch = palette(name)
                val selectedTheme = theme == name
                val tile = LinearLayout(this).apply {
                    orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL
                    setPadding(dp(10), dp(9), dp(9), dp(9)); minimumHeight = dp(76)
                    background = GradientDrawable().apply {
                        setColor(blend(swatch[1], swatch[4], 0.13f))
                        cornerRadius = dp(8).toFloat()
                        setStroke(dp(if (selectedTheme) 3 else 1), swatch[4])
                    }
                    isClickable = true; isFocusable = true
                    contentDescription = "$name theme. ${themeVibe(name)}${if (selectedTheme) ". Currently selected." else ". Tap to select."}"
                    setOnClickListener {
                        if (theme != name) {
                            theme = name; colors = palette(theme)
                            getSharedPreferences("prefs", 0).edit().putString("theme", theme).apply()
                            showSettingsScreen()
                        }
                    }
                }
                tile.addView(TextView(this).apply { text = themeIcon(name); textSize = 24f; setTextColor(swatch[4]); gravity = Gravity.CENTER }, LinearLayout.LayoutParams(dp(38), -1))
                val copy = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; gravity = Gravity.CENTER_VERTICAL; setPadding(dp(7), 0, 0, 0) }
                copy.addView(TextView(this).apply { text = name + if (selectedTheme) "  ✓" else ""; textSize = 14f; setTextColor(swatch[2]); typeface = Typeface.create("sans-serif-condensed", Typeface.BOLD); maxLines = 1; ellipsize = TextUtils.TruncateAt.END })
                copy.addView(TextView(this).apply { text = themeVibe(name); textSize = 10f; setTextColor(swatch[4]); maxLines = 2; ellipsize = TextUtils.TruncateAt.END })
                tile.addView(copy, LinearLayout.LayoutParams(0, -2, 1f))
                row.addView(tile, LinearLayout.LayoutParams(0, dp(82), 1f).apply { setMargins(dp(3), dp(3), dp(3), dp(3)) })
            }
            if (pair.size == 1) row.addView(View(this), LinearLayout.LayoutParams(0, dp(82), 1f))
            container.addView(row, LinearLayout.LayoutParams(-1, dp(88)))
        }
        val swatches = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL; setPadding(dp(12), dp(8), dp(12), dp(8)); background = surface(colors[3], colors[4]) }
        listOf("ACCENT" to colors[4], "BACKGROUND" to colors[0], "PANEL" to colors[1]).forEach { (label, color) ->
            val sample = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; gravity = Gravity.CENTER; setPadding(dp(4), dp(4), dp(4), dp(4)) }
            sample.addView(View(this).apply { background = GradientDrawable().apply { setColor(color); cornerRadius = dp(4).toFloat(); setStroke(dp(1), this@MainActivity.colors[2]) } }, LinearLayout.LayoutParams(dp(52), dp(24)))
            sample.addView(TextView(this).apply { text = label; textSize = 10f; setTextColor(colors[2]); gravity = Gravity.CENTER; setPadding(0, dp(3), 0, 0) })
            swatches.addView(sample, LinearLayout.LayoutParams(0, -2, 1f))
        }
        container.addView(swatches, LinearLayout.LayoutParams(-1, -2))
        container.addView(label("${themeIcon(theme)}  ${themeVibe(theme)}"))
    }

    private fun buildSourcesSettings(container: LinearLayout) {
        container.addView(label("CHEAT SOURCES"))
        container.addView(label("Install or update each source independently. Turn a source off to hide its entries from the game list without deleting them."))
        val sources = listOf(
            "CWCheat Database Plus — Saramagrean" to "https://github.com/Saramagrean/CWCheat-Database-Plus-/archive/refs/heads/master.zip",
            "PPSSPP workarounds — LunaMoo" to "https://github.com/LunaMoo/PPSSPP_workarounds/archive/refs/heads/master.zip"
        )
        sources.forEach { (name, url) ->
            val card = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(8, 5, 8, 5); background = surface(colors[3], colors[4]) }
            val top = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL }
            top.addView(TextView(this).apply { text = name; textSize = 14f; setTextColor(colors[2]); typeface = Typeface.create("sans-serif-condensed", Typeface.BOLD) }, LinearLayout.LayoutParams(0, -2, 1f))
            val enabled = CheckBox(this).apply { text = "Enabled"; setTextColor(colors[2]); buttonTintList = android.content.res.ColorStateList.valueOf(colors[4]); isChecked = sourceIsEnabled(name); setOnCheckedChangeListener { _, on -> setSourceEnabled(name, on); if (currentScreen == "mods") renderResults() } }
            top.addView(enabled)
            card.addView(top)
            card.addView(TextView(this).apply { text = url; textSize = 10f; setTextColor(colors[4]); maxLines = 2; ellipsize = TextUtils.TruncateAt.END })
            card.addView(button("UPDATE / INSTALL") { confirmAndDownload(url, name) })
            container.addView(card)
        }
        val prefs = getSharedPreferences("prefs", 0)
        val savedCustomName = prefs.getString("custom_source_name", "").orEmpty()
        val savedCustomUrl = prefs.getString("custom_source_url", "").orEmpty()
        if (savedCustomName.isNotBlank() && savedCustomUrl.isNotBlank()) {
            val card = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(8, 5, 8, 5); background = surface(colors[3], colors[4]) }
            val row = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL }
            row.addView(TextView(this).apply { text = savedCustomName; setTextColor(colors[2]); textSize = 14f }, LinearLayout.LayoutParams(0, -2, 1f))
            row.addView(CheckBox(this).apply { text = "Enabled"; setTextColor(colors[2]); isChecked = sourceIsEnabled(savedCustomName); buttonTintList = android.content.res.ColorStateList.valueOf(colors[4]); setOnCheckedChangeListener { _, on -> setSourceEnabled(savedCustomName, on); if (currentScreen == "mods") renderResults() } })
            card.addView(row)
            card.addView(TextView(this).apply { text = savedCustomUrl; textSize = 10f; setTextColor(colors[4]); maxLines = 2; ellipsize = TextUtils.TruncateAt.END })
            card.addView(button("UPDATE USER SOURCE") { confirmAndDownload(savedCustomUrl, savedCustomName) })
            container.addView(card)
        }
        container.addView(label("YOUR OWN SOURCE"))
        val custom = edit("Paste a direct HTTPS .zip / .db / .ini URL")
        custom.setText(customSourceUrl); container.addView(custom)
        container.addView(button("ADD / UPDATE USER SOURCE") {
            val link = custom.text.toString().trim()
            if (!link.startsWith("https://", true)) { status.text = "Use a secure HTTPS link to a cheat database or ZIP."; return@button }
            customSourceUrl = link
            val name = "User source — ${Uri.parse(link).host ?: "custom"}"
            getSharedPreferences("prefs", 0).edit().putString("custom_source_url", link).putString("custom_source_name", name).apply()
            confirmAndDownload(link, name); showSettingsScreen()
        })
    }

    private fun buildCoverArtSettings(container: LinearLayout) {
        container.addView(label("BOX ART SEARCH"))
        container.addView(label("Free Libretro PSP box art is searched automatically. If it has no match, you can optionally try SteamGridDB using your own API key."))
        val enabled = CheckBox(this).apply {
            text = "Use SteamGridDB as a fallback"
            setTextColor(colors[2]); buttonTintList = android.content.res.ColorStateList.valueOf(colors[4])
            isChecked = getSharedPreferences("prefs", 0).getBoolean("steamgrid_cover_enabled", false)
            setOnCheckedChangeListener { _, checked -> getSharedPreferences("prefs", 0).edit().putBoolean("steamgrid_cover_enabled", checked).apply() }
        }
        container.addView(enabled)
        container.addView(label("Create an API key in your SteamGridDB account, then paste it below. This is an optional SteamGridDB key, not your Steam password. The app encrypts and stores it on this device."))
        val keyField = edit("SteamGridDB API key").apply { inputType = InputType.TYPE_CLASS_TEXT or InputType.TYPE_TEXT_VARIATION_PASSWORD }
        container.addView(keyField)
        container.addView(label(if (getSteamGridApiKey().isNullOrBlank()) "No API key saved." else "An API key is saved securely on this device."))
        container.addView(button("SAVE API KEY") {
            val key = keyField.text.toString().trim()
            if (key.isBlank()) { status.text = "Paste your SteamGridDB API key first."; return@button }
            try {
                saveSteamGridApiKey(key)
                enabled.isChecked = true
                keyField.setText("")
                status.text = "SteamGridDB API key saved securely. Cover art will try it after Libretro."
                Toast.makeText(this, "SteamGridDB key saved.", Toast.LENGTH_SHORT).show()
            } catch (_: Exception) { status.text = "Could not secure the API key on this device." }
        })
        container.addView(button("REMOVE SAVED API KEY") {
            getSharedPreferences("prefs", 0).edit().remove("steamgrid_api_key_enc").putBoolean("steamgrid_cover_enabled", false).apply()
            status.text = "Saved SteamGridDB API key removed."
            showSettingsScreen()
        })
        container.addView(button("GET / MANAGE STEAMGRIDDB API KEY") {
            try { startActivity(Intent(Intent.ACTION_VIEW, Uri.parse("https://www.steamgriddb.com/profile/preferences"))) }
            catch (_: Exception) { status.text = "Could not open the SteamGridDB key page." }
        })
    }

    private fun coverArtKey(): SecretKey {
        val alias = "pspcheatdb.coverart.api"
        val store = KeyStore.getInstance("AndroidKeyStore").apply { load(null) }
        (store.getKey(alias, null) as? SecretKey)?.let { return it }
        val generator = KeyGenerator.getInstance(KeyProperties.KEY_ALGORITHM_AES, "AndroidKeyStore")
        generator.init(KeyGenParameterSpec.Builder(alias, KeyProperties.PURPOSE_ENCRYPT or KeyProperties.PURPOSE_DECRYPT)
            .setBlockModes(KeyProperties.BLOCK_MODE_GCM).setEncryptionPaddings(KeyProperties.ENCRYPTION_PADDING_NONE)
            .setRandomizedEncryptionRequired(true).build())
        return generator.generateKey()
    }

    private fun saveSteamGridApiKey(value: String) {
        val cipher = Cipher.getInstance("AES/GCM/NoPadding")
        cipher.init(Cipher.ENCRYPT_MODE, coverArtKey())
        val encrypted = cipher.doFinal(value.toByteArray(Charsets.UTF_8))
        val packed = cipher.iv + encrypted
        getSharedPreferences("prefs", 0).edit().putString("steamgrid_api_key_enc", Base64.encodeToString(packed, Base64.NO_WRAP)).apply()
    }

    private fun getSteamGridApiKey(): String? {
        return try {
            val packed = Base64.decode(getSharedPreferences("prefs", 0).getString("steamgrid_api_key_enc", null), Base64.NO_WRAP)
            if (packed.size <= 12) return null
            val cipher = Cipher.getInstance("AES/GCM/NoPadding")
            cipher.init(Cipher.DECRYPT_MODE, coverArtKey(), GCMParameterSpec(128, packed.copyOfRange(0, 12)))
            String(cipher.doFinal(packed.copyOfRange(12, packed.size)), Charsets.UTF_8)
        } catch (_: Exception) { null }
    }

    private fun fetchSteamGridBoxArt(technicalTitle: String, gameId: String, apiKey: String): ByteArray? {
        val apiRoot = "https://www.steamgriddb.com/api/v2"
        val searchTerms = listOf(technicalTitle, gameId).map(String::trim).filter(String::isNotBlank).distinct()
        var gridId: Int? = null
        for (term in searchTerms) {
            val encoded = URLEncoder.encode(term, "UTF-8").replace("+", "%20")
            val search = steamGridApiJson("$apiRoot/search/autocomplete/$encoded", apiKey) ?: continue
            gridId = search.optJSONArray("data")?.optJSONObject(0)?.optInt("id")?.takeIf { it > 0 }
            if (gridId != null) break
        }
        val id = gridId ?: return null
        val gridsUrl = "$apiRoot/grids/game/$id?dimensions=600x900%2C342x482%2C660x930&types=static&nsfw=false&humor=false&epilepsy=false&page=0"
        val grids = steamGridApiJson(gridsUrl, apiKey)?.optJSONArray("data") ?: return null
        val coverUrl = (0 until grids.length()).asSequence().mapNotNull { index ->
            grids.optJSONObject(index)?.optString("url")?.takeIf { it.startsWith("https://") }
        }.firstOrNull() ?: return null
        val connection = URL(coverUrl).openConnection() as HttpURLConnection
        return try {
            connection.connectTimeout = 3000; connection.readTimeout = 5000; connection.instanceFollowRedirects = true
            if (connection.responseCode != HttpURLConnection.HTTP_OK) null
            else connection.inputStream.use { readLimited(it, 4 * 1024 * 1024) }
        } finally { connection.disconnect() }
    }

    private fun steamGridApiJson(url: String, apiKey: String): JSONObject? {
        val connection = URL(url).openConnection() as HttpURLConnection
        return try {
            connection.connectTimeout = 2500; connection.readTimeout = 3500; connection.instanceFollowRedirects = true
            connection.setRequestProperty("Authorization", "Bearer $apiKey")
            connection.setRequestProperty("Accept", "application/json")
            if (connection.responseCode == HttpURLConnection.HTTP_UNAUTHORIZED) throw SecurityException("SteamGridDB API key was rejected")
            if (connection.responseCode != HttpURLConnection.HTTP_OK) null
            else JSONObject(connection.inputStream.use { readLimited(it, 1024 * 1024).toString(Charsets.UTF_8) })
        } finally { connection.disconnect() }
    }

    private fun fetchLibretroIndexedCover(gameTitle: String, id: String, region: String, cacheDir: File): ByteArray? {
        val base = "https://thumbnails.libretro.com/Sony%20-%20PlayStation%20Portable/Named_Boxarts/"
        val indexFile = File(cacheDir, "_named_boxarts_index.html")
        val indexText = if (indexFile.isFile && System.currentTimeMillis() - indexFile.lastModified() < 7L * 24 * 60 * 60 * 1000) {
            indexFile.readText(Charsets.UTF_8)
        } else {
            val indexConnection = URL(base).openConnection() as HttpURLConnection
            try {
                indexConnection.connectTimeout = 2500; indexConnection.readTimeout = 6000; indexConnection.instanceFollowRedirects = true
                indexConnection.setRequestProperty("User-Agent", "PSP-Cheat-DB-Manager-Android/0.7.1")
                if (indexConnection.responseCode != HttpURLConnection.HTTP_OK) return null
                indexConnection.inputStream.use { readLimited(it, 12 * 1024 * 1024).toString(Charsets.UTF_8) }.also { indexFile.writeText(it, Charsets.UTF_8) }
            } finally { indexConnection.disconnect() }
        }
        val wanted = normalizeCoverName(gameTitle)
        if (wanted.isBlank()) return null
        val fileNames = Regex("href\\s*=\\s*[\"']([^\"']+\\.png)[\"']", RegexOption.IGNORE_CASE).findAll(indexText)
            .mapNotNull { match -> try { URLDecoder.decode(match.groupValues[1].substringAfterLast('/').substringBefore('?'), "UTF-8") } catch (_: Exception) { null } }
            .toList()
        val matches = fileNames.filter { normalizeCoverName(it.substringBeforeLast('.')) == wanted || normalizeCoverName(it.substringBeforeLast('.')) == id.lowercase(Locale.ROOT) }
        val preferred = matches.sortedBy { file ->
            val wantedRegion = when {
                region.contains("europe", true) || region.equals("eu", true) -> "Europe"
                region.contains("usa", true) || region.contains("united states", true) || region.contains("north america", true) -> "USA"
                region.contains("japan", true) || region.equals("jp", true) -> "Japan"
                region.contains("korea", true) -> "Korea"
                region.contains("australia", true) -> "Australia"
                else -> ""
            }
            val regionPenalty = if (wantedRegion.isNotBlank() && file.contains("($wantedRegion", true)) 0 else 1
            val variantPenalty = when {
                file.contains("(Demo)", true) || file.contains("(Beta)", true) || file.contains("(Promo)", true) -> 4
                Regex("\\(v\\d", RegexOption.IGNORE_CASE).containsMatchIn(file) -> 2
                else -> 0
            }
            regionPenalty * 10 + variantPenalty
        }.firstOrNull() ?: return null
        val imageUrl = base + URLEncoder.encode(preferred, "UTF-8").replace("+", "%20")
        val imageConnection = URL(imageUrl).openConnection() as HttpURLConnection
        return try {
            imageConnection.connectTimeout = 2500; imageConnection.readTimeout = 5000; imageConnection.instanceFollowRedirects = true
            if (imageConnection.responseCode != HttpURLConnection.HTTP_OK) null
            else imageConnection.inputStream.use { readLimited(it, 4 * 1024 * 1024) }
        } finally { imageConnection.disconnect() }
    }

    private fun normalizeCoverName(value: String): String = value
        .replace(Regex("\\s*\\[(?:EU|EUR|EUROPE|USA|US|JP|JPN|JAPAN|WORLD)\\]", RegexOption.IGNORE_CASE), "")
        .replace(Regex("\\s*\\((?:Europe|Europe, Australia|USA|Japan|Korea|Asia|World|UK)[^)]*\\)", RegexOption.IGNORE_CASE), "")
        .replace(Regex("\\s*\\((?:En|Fr|De|Es|It|Ja|Zh|Ko)(?:,[A-Za-z]{2,3})*\\)", RegexOption.IGNORE_CASE), "")
        .replace(Regex("\\s*\\(v\\d+(?:\\.\\d+)*\\)", RegexOption.IGNORE_CASE), "")
        .lowercase(Locale.ROOT).replace(Regex("[^a-z0-9]"), "")

    private fun confirmAndDownload(url: String, name: String) {
        if (name.startsWith("User source")) getSharedPreferences("prefs", 0).edit().putString("custom_source_name", name).putString("custom_source_url", url).apply()
        AlertDialog.Builder(this).setTitle("Update source?").setMessage("Download and merge $name? This uses your internet connection. Existing entries are retained and duplicates are skipped.")
            .setNegativeButton("Cancel", null).setPositiveButton("Update") { _, _ -> downloadSource(url, name) }.showThemed()
    }

    private fun sourceIsEnabled(name: String): Boolean = !(getSharedPreferences("prefs", 0).getStringSet("disabled_sources", emptySet()) ?: emptySet()).contains(name)
    private fun setSourceEnabled(name: String, enabled: Boolean) {
        val pref = getSharedPreferences("prefs", 0); val disabled = pref.getStringSet("disabled_sources", emptySet())?.toMutableSet() ?: mutableSetOf()
        if (enabled) disabled.remove(name) else disabled.add(name)
        pref.edit().putStringSet("disabled_sources", disabled).apply()
    }

    private fun resetAppToFreshInstall() {
        AlertDialog.Builder(this).setTitle("Reset everything?").setMessage("This clears every imported cheat, saved source, theme choice, recent game, favorite, and selected folder. Continue?").setNegativeButton("Cancel", null).setPositiveButton("Continue") { _, _ ->
            AlertDialog.Builder(this).setTitle("Final confirmation").setMessage("The cheat database will be deleted and cannot be recovered from this app. Reset to a fresh install now?").setNegativeButton("Keep my data", null).setPositiveButton("Reset app") { _, _ ->
                deleteFile("cheats.json"); deleteFile(TITLE_CATALOG_FILE); getSharedPreferences("prefs", 0).edit().clear().apply(); selected.clear(); titleCatalog.clear(); customSourceUrl = ""; currentGameId = ""; currentScreen = "search"; theme = "Ghost Protocol"; colors = palette(theme); settingsTab = "General"
                val coverDir = File(filesDir, "psp-covers"); coverDir.listFiles()?.forEach { it.delete() }
                buildUi(); showWelcomeIfNeeded(); loadTitleCatalog()
            }.showThemed()
        }.showThemed()
    }

    private fun gameFolderText(): String {
        val saved = getSharedPreferences("prefs", 0).getString(GAME_TREE_PREF, null) ?: return "No game folder selected. You can still choose each ISO/PBP/CHD with Load Game File."
        return "Remembered game folder: ${Uri.parse(saved).lastPathSegment.orEmpty().substringAfterLast(':').substringAfterLast('/')}"
    }
    private fun chooseGameFolder(scanAfterSelection: Boolean = false) {
        pendingFolderScanAfterPick = scanAfterSelection
        val intent = Intent(Intent.ACTION_OPEN_DOCUMENT_TREE)
        getSharedPreferences("prefs", 0).getString(GAME_TREE_PREF, null)?.let { saved -> if (android.os.Build.VERSION.SDK_INT >= 26) intent.putExtra(DocumentsContract.EXTRA_INITIAL_URI, Uri.parse(saved)) }
        try { startActivityForResult(intent, REQ_GAME_FOLDER) } catch (e: Exception) { pendingFolderScanAfterPick = false; status.text = "Could not open folder picker: ${e.message}" }
    }
    private fun saveGameFolder(uri: Uri) {
        val shouldScan = pendingFolderScanAfterPick
        pendingFolderScanAfterPick = false
        try {
            contentResolver.takePersistableUriPermission(uri, Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_WRITE_URI_PERMISSION)
            getSharedPreferences("prefs", 0).edit().putString(GAME_TREE_PREF, uri.toString()).apply()
            if (currentScreen == "settings") showSettingsScreen()
            tutorialFolderLabel?.text = "Selected folder: ${uri.lastPathSegment.orEmpty().substringAfterLast(':').substringAfterLast('/')}"
            showCornerNotification("Game folder saved")
            if (shouldScan) startFullFolderScan(uri)
        } catch (e: Exception) { if (::status.isInitialized) status.text = "Could not remember that folder: ${e.message}" }
    }
    private fun showGameImportOptions() {
        val options = if ((getSharedPreferences("prefs", 0).getString("preferred_game_import", "single") ?: "single") == "folder")
            arrayOf("Scan a full games folder", "Add one ISO / PBP / CHD file")
        else arrayOf("Add one ISO / PBP / CHD file", "Scan a full games folder")
        AlertDialog.Builder(this).setTitle("Add PSP games")
            .setItems(options) { _, which ->
                val folder = options[which].startsWith("Scan")
                getSharedPreferences("prefs", 0).edit().putString("preferred_game_import", if (folder) "folder" else "single").apply()
                if (folder) confirmFullFolderScan() else openDocument(REQ_GAME)
            }.setNegativeButton("Cancel", null).showThemed()
    }
    private fun confirmFullFolderScan() {
        AlertDialog.Builder(this).setTitle("Scan a games folder?")
            .setMessage("The app will search the selected folder and its subfolders for ISO, PBP, and CHD games, add them to your library, and look for cover art in the background. Large libraries can take several minutes; you can keep using the app while it scans.")
            .setNegativeButton("Cancel", null)
            .setPositiveButton(if (getSharedPreferences("prefs", 0).getString(GAME_TREE_PREF, null) == null) "Choose folder" else "Start scan") { _, _ ->
                val saved = getSharedPreferences("prefs", 0).getString(GAME_TREE_PREF, null)
                if (saved == null) chooseGameFolder(scanAfterSelection = true) else startFullFolderScan(Uri.parse(saved))
            }.showThemed()
    }
    private fun startFullFolderScan(tree: Uri) {
        if (folderScanDialogText != null) return
        val dialogBody = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(dp(20), dp(8), dp(20), dp(8)) }
        folderScanDialogText = label("Starting folder scan…")
        dialogBody.addView(folderScanDialogText)
        dialogBody.addView(ProgressBar(this).apply { isIndeterminate = true; indeterminateTintList = android.content.res.ColorStateList.valueOf(colors[4]) }, LinearLayout.LayoutParams(-1, dp(10)))
        val dialog = AlertDialog.Builder(this).setTitle("Scanning PSP games")
            .setView(dialogBody).setPositiveButton("Continue in background", null).setNegativeButton("Close", null).create()
        dialog.setOnShowListener {
            styleDialog(dialog)
            dialog.getButton(AlertDialog.BUTTON_POSITIVE).setOnClickListener { dialog.dismiss() }
            dialog.getButton(AlertDialog.BUTTON_NEGATIVE).setOnClickListener { dialog.dismiss() }
        }
        dialog.setOnDismissListener { folderScanDialogText = null }
        dialog.show()
        val uiStart = System.currentTimeMillis()
        folderScanWorker.execute {
            val discovered = linkedMapOf<String, String>()
            val visited = hashSetOf<String>()
            val stack = java.util.ArrayDeque<String>()
            var examined = 0
            try {
                val rootDoc = DocumentsContract.getTreeDocumentId(tree)
                stack.add(rootDoc)
                while (stack.isNotEmpty()) {
                    val docId = stack.removeLast()
                    if (!visited.add(docId)) continue
                    val children = DocumentsContract.buildChildDocumentsUriUsingTree(tree, docId)
                    contentResolver.query(children, arrayOf(DocumentsContract.Document.COLUMN_DOCUMENT_ID, DocumentsContract.Document.COLUMN_DISPLAY_NAME, DocumentsContract.Document.COLUMN_MIME_TYPE), null, null, null)?.use { cursor ->
                        val idCol = cursor.getColumnIndexOrThrow(DocumentsContract.Document.COLUMN_DOCUMENT_ID)
                        val nameCol = cursor.getColumnIndexOrThrow(DocumentsContract.Document.COLUMN_DISPLAY_NAME)
                        val mimeCol = cursor.getColumnIndexOrThrow(DocumentsContract.Document.COLUMN_MIME_TYPE)
                        while (cursor.moveToNext()) {
                            examined++
                            val childId = cursor.getString(idCol) ?: continue
                            val name = cursor.getString(nameCol).orEmpty()
                            val mime = cursor.getString(mimeCol).orEmpty()
                            if (mime == DocumentsContract.Document.MIME_TYPE_DIR) stack.add(childId)
                            else if (name.substringAfterLast('.', "").lowercase(Locale.ROOT) in setOf("iso", "pbp", "chd")) {
                                val serial = SERIAL_PATTERN.find(name.uppercase(Locale.ROOT))?.let { it.groupValues[1] + it.groupValues[2] }
                                val matched = serial ?: titleCatalog.firstOrNull { normalizeCoverName(it.title) == normalizeCoverName(name.substringBeforeLast('.', name)) }?.id
                                if (matched != null) discovered.putIfAbsent(matched, name.substringBeforeLast('.', name))
                            }
                            if (examined % 50 == 0 && System.currentTimeMillis() - uiStart > 500) runOnUiThread {
                                folderScanDialogText?.text = "Checked $examined folders/files · found ${discovered.size} games…"
                                if (::status.isInitialized) status.text = "Scanning game folder… $examined entries checked"
                            }
                        }
                    }
                }
                val prefs = getSharedPreferences("prefs", 0)
                val oldIds = try { JSONArray(prefs.getString("library_game_ids", "[]")) } catch (_: Exception) { JSONArray() }
                val mergedIds = (0 until oldIds.length()).map { oldIds.optString(it) }.filter(String::isNotBlank).toMutableList()
                val titles = try { JSONObject(prefs.getString("library_game_titles", "{}") ?: "{}") } catch (_: Exception) { JSONObject() }
                discovered.forEach { (id, title) -> if (id !in mergedIds) mergedIds.add(id); titles.put(id, title) }
                prefs.edit().putString("library_game_ids", JSONArray(mergedIds).toString()).putString("library_game_titles", titles.toString()).apply()
                runOnUiThread {
                    folderScanDialogText?.text = "Finished: found ${discovered.size} identifiable games among $examined entries. Cover art will load as you browse."
                    if (::status.isInitialized) status.text = "Folder scan complete · ${discovered.size} games found"
                    showCornerNotification("Scan finished · ${discovered.size} games found")
                    if (currentScreen == "games") openGamesScreen()
                    discovered.forEach { (id, fileTitle) ->
                        val meta = titleCatalog.firstOrNull { it.id == id }
                        loadCoverArt(id, meta?.title ?: fileTitle, meta?.region.orEmpty(), ImageView(this))
                    }
                    Handler(Looper.getMainLooper()).postDelayed({ folderScanDialogText = null }, 7000)
                }
            } catch (e: Exception) {
                runOnUiThread {
                    folderScanDialogText?.text = "Folder scan stopped: ${e.message ?: e.javaClass.simpleName}"
                    if (::status.isInitialized) status.text = "Folder scan failed: ${e.message ?: e.javaClass.simpleName}"
                    showCornerNotification("Game folder scan failed", isError = true)
                    Handler(Looper.getMainLooper()).postDelayed({ folderScanDialogText = null }, 7000)
                }
            }
        }
    }
    private fun rememberRecentGame(id: String) {
        val pref = getSharedPreferences("prefs", 0); val old = try { JSONArray(pref.getString("recent_game_ids", "[]")) } catch (_: Exception) { JSONArray() }
        val ids = (0 until old.length()).mapNotNull { old.optString(it).takeIf(String::isNotBlank) }.filter { it != id }.toMutableList()
        ids.add(0, id); val out = JSONArray(); ids.take(20).forEach(out::put); pref.edit().putString("recent_game_ids", out.toString()).apply()
    }
    private fun readRecentGameIds(): List<String> {
        return try {
            val saved = JSONArray(getSharedPreferences("prefs", 0).getString("recent_game_ids", "[]"))
            (0 until saved.length()).mapNotNull { saved.optString(it).takeIf(String::isNotBlank) }
        } catch (_: Exception) { emptyList() }
    }
    private fun favoriteIds(): MutableSet<String> = getSharedPreferences("prefs", 0).getStringSet("favorite_game_ids", emptySet())?.toMutableSet() ?: mutableSetOf()
    private fun isFavorite(id: String) = id in favoriteIds()
    private fun toggleFavoriteOnly(id: String) {
        if (id.isBlank()) return
        val ids = favoriteIds(); if (!ids.add(id)) ids.remove(id)
        getSharedPreferences("prefs", 0).edit().putStringSet("favorite_game_ids", ids).apply()
        if (::quickFavoriteButton.isInitialized && currentScreen == "search") quickFavoriteButton.text = if (isFavorite(id)) "★  FAVORITED" else "☆  QUICK FAVORITE"
    }
    private fun toggleFavorite(id: String) { toggleFavoriteOnly(id); openModsScreen(id) }
    private fun activeGameId(): String {
        val typed = if (::gameId.isInitialized) gameId.text.toString().uppercase().replace(Regex("[-_ ]"), "").trim() else ""
        return typed.takeIf { currentScreen == "search" && it.matches(Regex("[A-Z]{4}\\d{5}")) }
            ?: currentGameId.takeIf { it.isNotBlank() } ?: typed
    }
    private fun toggleQuickFavorite() {
        val id = if (currentScreen in setOf("games", "recent", "favorites") && focusedGameRowId.isNotBlank()) focusedGameRowId else activeGameId()
        if (!id.matches(Regex("[A-Z]{4}\\d{5}"))) { if (::status.isInitialized) status.text = "Choose a game before adding a favorite."; return }
        toggleFavoriteOnly(id)
        when (currentScreen) {
            "games", "recent", "favorites" -> openCollectionScreen(currentScreen)
            "mods" -> openModsScreen(id)
            "search" -> if (::status.isInitialized) status.text = if (isFavorite(id)) "Added $id to Favorites." else "Removed $id from Favorites."
        }
    }
    private fun normalizeControllerStyle(style: String): String = when (style) {
        "Retro / PlayStation", "PlayStation" -> "PlayStation"
        "Xbox" -> "Xbox"
        else -> "Switch"
    }
    private fun controllerGlyph(button: String): String = when (controllerStyle) {
        "PlayStation" -> when (button) { "A" -> "✕"; "B" -> "○"; "X" -> "□"; "Y" -> "△"; "L2" -> "L2"; "START" -> "OPTIONS"; else -> button }
        "Switch" -> when (button) { "A" -> "Ⓐ"; "B" -> "Ⓑ"; "X" -> "Ⓧ"; "Y" -> "Ⓨ"; "R1" -> "R"; "L1" -> "L"; "L2" -> "ZL"; "START" -> "+"; else -> button }
        else -> when (button) { "L1" -> "LB"; "R1" -> "RB"; "L2" -> "LT"; "START" -> "MENU"; else -> button }
    }
    private fun controllerFooter(screen: String): TextView {
        val pieces = mutableListOf("${controllerGlyph("A")} SELECT", "${controllerGlyph("B")} BACK")
        if (screen == "mods") pieces.add("${controllerGlyph("X")} FILTER")
        if (screen == "mods" || screen in setOf("games", "recent", "favorites")) pieces.add("${controllerGlyph("Y")} SORT")
        if (screen in setOf("games", "recent", "favorites")) pieces.add("${controllerGlyph("L2")} VIEW")
        if (screen != "settings") pieces.add("${controllerGlyph("R1")} FAVORITE")
        if (screen == "home") pieces.add("${controllerGlyph("Y")} GAMES")
        pieces.add("${controllerGlyph("START")} ${if (screen == "settings") "HOME" else "SETTINGS"}")
        return TextView(this).apply {
            text = pieces.joinToString("     ·     "); setTextColor(colors[4]); textSize = if (compactLandscape()) 10f else 12f
            typeface = Typeface.create("sans-serif-condensed", Typeface.BOLD); gravity = Gravity.CENTER
            maxLines = 1; ellipsize = TextUtils.TruncateAt.END; setPadding(dp(6), dp(6), dp(6), dp(5)); background = surface(colors[1], colors[4])
            contentDescription = "Controller shortcuts: ${pieces.joinToString(", ")}"
        }
    }
    private fun readLibraryGameIds(): List<String> = try {
        val saved = JSONArray(getSharedPreferences("prefs", 0).getString("library_game_ids", "[]"))
        (0 until saved.length()).mapNotNull { saved.optString(it).takeIf(String::isNotBlank) }
    } catch (_: Exception) { emptyList() }
    private fun readLibraryTitle(id: String): String = try { JSONObject(getSharedPreferences("prefs", 0).getString("library_game_titles", "{}") ?: "{}").optString(id, id) ?: id } catch (_: Exception) { id }
    private fun showRecentOrFavoriteList(favorites: Boolean) = openCollectionScreen(if (favorites) "favorites" else "recent")
    private fun openCollectionScreen(mode: String) {
        autoSearch?.let { autoSearchHandler.removeCallbacks(it) }; autoSearch = null
        libraryMode = mode
        currentScreen = mode
        recentCoverViews.clear(); recentCoverStatusViews.clear()
        val compact = compactLandscape()
        val titleText = when (mode) { "favorites" -> "FAVORITES"; "recent" -> "RECENTLY LOADED GAMES"; else -> "GAME LIBRARY" }
        val rawIds = when (mode) { "favorites" -> favoriteIds().toList(); "recent" -> readRecentGameIds(); else -> (readLibraryGameIds() + readRecentGameIds()).distinct() }
        val ids = when (gameSortMode) {
            "Title A–Z" -> rawIds.sortedBy { (titleCatalog.firstOrNull { item -> item.id == it }?.title ?: db[it]?.title ?: readLibraryTitle(it)).lowercase(Locale.ROOT) }
            "Title Z–A" -> rawIds.sortedByDescending { (titleCatalog.firstOrNull { item -> item.id == it }?.title ?: db[it]?.title ?: readLibraryTitle(it)).lowercase(Locale.ROOT) }
            "Region" -> rawIds.sortedBy { titleCatalog.firstOrNull { item -> item.id == it }?.region.orEmpty() }
            else -> rawIds
        }
        val page = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(8, 7, 8, 6); setBackgroundColor(colors[0]) }
        val head = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL; setPadding(8, 4, 8, 4); background = surface(colors[3], colors[4]) }
        head.addView(button("‹") { returnToSearch() }.apply { contentDescription = "Home" }, LinearLayout.LayoutParams(dp(48), if (compact) 44 else 50))
        head.addView(TextView(this).apply { text = titleText; textSize = if (compact) 17f else 21f; setTextColor(colors[2]); typeface = Typeface.create("sans-serif-condensed", Typeface.BOLD); gravity = Gravity.CENTER_VERTICAL; setPadding(dp(10), 0, 0, 0) }, LinearLayout.LayoutParams(0, if (compact) 44 else 50, 1f))
        head.addView(button("▦ VIEW") { showCoverLayoutPicker() }.apply { contentDescription = "Change game display layout · current: $coverLayout" })
        head.addView(button("⇅  ${gameSortMode.uppercase(Locale.ROOT)}") { showGameSortPicker() })
        if (mode == "games") head.addView(button("＋ ADD GAMES") { showGameImportOptions() })
        page.addView(head)
        val isGrid = coverLayout == "12-Game Grid"
        val isCarousel = coverLayout == "Cover Carousel"
        val list: ViewGroup = if (isGrid) GridLayout(this).apply {
            columnCount = 3; alignmentMode = GridLayout.ALIGN_BOUNDS; useDefaultMargins = false
            setPadding(dp(3), dp(5), dp(3), dp(8))
        } else LinearLayout(this).apply {
            orientation = if (isCarousel) LinearLayout.HORIZONTAL else LinearLayout.VERTICAL
            setPadding(dp(5), dp(6), dp(5), dp(8))
            clipChildren = false; clipToPadding = false
        }
        if (ids.isEmpty()) {
            val emptyText = when (mode) { "favorites" -> "No favorites yet. Open a game and tap Add Favorite to keep it here."; "recent" -> "No recent games yet. Add or open a game and it will appear here."; else -> "Your game library is empty. Add one game file or scan a full folder." }
            list.addView(TextView(this).apply { text = emptyText; textSize = 16f; setTextColor(colors[4]); gravity = Gravity.CENTER; setPadding(dp(24), dp(24), dp(24), dp(24)) })
            if (mode == "games") list.addView(button("ADD PSP GAMES") { showGameImportOptions() })
            list.addView(button("SEARCH THE PSP GAME CATALOG") { returnToSearch(); showTitlePicker() })
        } else ids.forEach { id ->
            val meta = titleCatalog.firstOrNull { it.id == id }
            val gameTitle = meta?.title ?: db[id]?.title?.takeIf { it.isNotBlank() } ?: readLibraryTitle(id)
            val region = meta?.region ?: ""
            val stacked = coverLayout == "Stacked" || isGrid || isCarousel
            val compactDetails = coverLayout == "Compact Details"
            val card = LinearLayout(this).apply {
                orientation = if (stacked) LinearLayout.VERTICAL else LinearLayout.HORIZONTAL
                gravity = if (stacked) Gravity.CENTER_HORIZONTAL else Gravity.CENTER_VERTICAL
                setPadding(dp(if (coverLayout == "Snug") 5 else 8), dp(7), dp(if (coverLayout == "Snug") 5 else 8), dp(7))
                background = surface(colors[1], colors[4]); isClickable = true; isFocusable = true; tag = id
                setOnFocusChangeListener { view, hasFocus ->
                    if (hasFocus) focusedGameRowId = id
                    if (isCarousel) {
                        view.animate().scaleX(if (hasFocus) 1.08f else 1f).scaleY(if (hasFocus) 1.08f else 1f).setDuration(150).start()
                        view.elevation = if (hasFocus) dp(12).toFloat() else dp(1).toFloat()
                    }
                }
                if (isCarousel) setOnHoverListener { view, event ->
                    val hovering = event.action == android.view.MotionEvent.ACTION_HOVER_ENTER || event.action == android.view.MotionEvent.ACTION_HOVER_MOVE
                    val leaving = event.action == android.view.MotionEvent.ACTION_HOVER_EXIT
                    if (hovering || leaving) view.animate().scaleX(if (hovering) 1.08f else 1f).scaleY(if (hovering) 1.08f else 1f).setDuration(150).start()
                    false
                }
                setOnClickListener { openModsScreen(id) }
            }
            val art = ImageView(this).apply { scaleType = ImageView.ScaleType.CENTER_CROP; setBackgroundColor(colors[3]); contentDescription = "$gameTitle cover art" }
            val artParams = when (coverLayout) {
                "12-Game Grid" -> LinearLayout.LayoutParams(dp(if (compact) 88 else 100), dp(if (compact) 132 else 150))
                "Cover Carousel" -> LinearLayout.LayoutParams(dp(if (compact) 92 else 120), dp(if (compact) 138 else 180))
                "Compact Details" -> LinearLayout.LayoutParams(dp(50), dp(75))
                "Stacked" -> LinearLayout.LayoutParams(dp(if (compact) 88 else 104), dp(if (compact) 132 else 156))
                "Snug" -> LinearLayout.LayoutParams(dp(if (compact) 48 else 56), dp(if (compact) 72 else 84))
                else -> LinearLayout.LayoutParams(dp(if (compact) 80 else 100), dp(if (compact) 120 else 150))
            }
            card.addView(art, artParams)
            val info = LinearLayout(this).apply {
                orientation = LinearLayout.VERTICAL
                gravity = if (stacked) Gravity.CENTER else Gravity.CENTER_VERTICAL
                setPadding(if (stacked) dp(5) else dp(if (coverLayout == "Snug") 7 else 12), if (stacked) dp(5) else 0, dp(4), 0)
            }
            info.addView(TextView(this).apply { text = gameTitle; textSize = if (isGrid || compactDetails || compact) 13f else 18f; setTextColor(colors[2]); typeface = Typeface.create("sans-serif-condensed", Typeface.BOLD); maxLines = if (isGrid) 1 else 2; ellipsize = TextUtils.TruncateAt.END; gravity = if (stacked) Gravity.CENTER else Gravity.START })
            info.addView(TextView(this).apply { text = if (isGrid) id else "$id  ·  ${if (region.isBlank()) "Region unknown" else countryName(region)}"; textSize = if (compact || compactDetails || isGrid) 10f else 14f; setTextColor(colors[4]); maxLines = 1; ellipsize = TextUtils.TruncateAt.END; setPadding(0, dp(3), 0, 0); gravity = if (stacked) Gravity.CENTER else Gravity.START })
            val artStatus = TextView(this).apply { text = "Checking cover art…"; textSize = if (compact) 11f else 12f; setTextColor(colors[4]); setPadding(0, dp(4), 0, 0) }
            if (!isGrid) info.addView(artStatus)
            if (compactDetails) {
                val available = db[id]?.cheats?.size ?: 0
                val chosen = selected.count { it.first == id }
                info.addView(TextView(this).apply { text = "$chosen selected for export · $available available"; textSize = 11f; setTextColor(colors[4]); maxLines = 1; ellipsize = TextUtils.TruncateAt.END; setPadding(0, dp(3), 0, 0) })
            } else if (!isGrid) info.addView(TextView(this).apply { text = "OPEN CHEAT DATABASE  ›"; textSize = if (compact) 11f else 12f; setTextColor(colors[2]); typeface = Typeface.create("sans-serif-condensed", Typeface.BOLD); setPadding(0, dp(5), 0, 0) })
            installedIniLine(id)?.let { iniText -> info.addView(TextView(this).apply { text = iniText; textSize = 10f; setTextColor(colors[4]); maxLines = 1; ellipsize = TextUtils.TruncateAt.END; setPadding(0, dp(3), 0, 0) }) }
            card.addView(info, if (stacked) LinearLayout.LayoutParams(-1, -2) else LinearLayout.LayoutParams(0, -2, 1f))
            if (mode == "games") card.addView(button(if (isFavorite(id)) "★" else "☆") { toggleFavoriteOnly(id); openCollectionScreen("games") }.apply { contentDescription = if (isFavorite(id)) "Remove from favorites" else "Add to favorites" })
            when {
                isGrid -> {
                    val cellWidth = ((resources.displayMetrics.widthPixels - dp(72)) / 3).coerceAtLeast(dp(100))
                    list.addView(card, GridLayout.LayoutParams().apply { width = cellWidth; height = -2; setMargins(dp(2), dp(2), dp(2), dp(5)) })
                }
                isCarousel -> list.addView(card, LinearLayout.LayoutParams(dp(if (compact) 190 else 238), -1).apply { setMargins(dp(8), dp(12), dp(8), dp(12)) })
                else -> list.addView(card, LinearLayout.LayoutParams(-1, -2).apply { bottomMargin = dp(6) })
            }
            recentCoverViews[id] = art; recentCoverStatusViews[id] = artStatus
        }
        val scroll: View = when {
            isCarousel -> HorizontalScrollView(this).apply { isFillViewport = true; clipChildren = false; clipToPadding = false; addView(list, android.widget.FrameLayout.LayoutParams(-2, -1)) }
            else -> ScrollView(this).apply { isFillViewport = true; addView(list) }
        }
        page.addView(scroll, LinearLayout.LayoutParams(-1, 0, 1f))
        status = label(if (installedIniScanComplete) installedIniSummary else if (ids.isEmpty()) "No games in this list yet." else "Select a game to open its available cheats.").apply { setTextColor(colors[4]) }
        page.addView(status)
        page.addView(controllerFooter(mode))
        setContentView(page)
        ids.forEach { id -> val meta = titleCatalog.firstOrNull { it.id == id }; recentCoverViews[id]?.let { loadCoverArt(id, meta?.title ?: db[id]?.title ?: readLibraryTitle(id), meta?.region.orEmpty(), it) } }
    }
    private fun openGamesScreen() = openCollectionScreen("games")
    private fun availableCoverLayouts() = listOf("Horizontal", "Snug", "Stacked", "Compact Details", "12-Game Grid", "Cover Carousel")
    private fun showCoverLayoutPicker() {
        val descriptions = mapOf(
            "Horizontal" to "Wide cover beside game details",
            "Snug" to "Small cover beside compact details",
            "Stacked" to "Cover above full game details",
            "Compact Details" to "Small covers plus selected and available mod counts",
            "12-Game Grid" to "Three columns by four rows with essential labels",
            "Cover Carousel" to "Large covers; focus or hover to enlarge"
        )
        val options = availableCoverLayouts().map { "${if (it == coverLayout) "✓  " else "   "}$it\n     ${descriptions[it]}" }.toTypedArray()
        AlertDialog.Builder(this).setTitle("Game display layout").setItems(options) { dialog, which ->
            coverLayout = availableCoverLayouts()[which]
            getSharedPreferences("prefs", 0).edit().putString("cover_layout", coverLayout).apply()
            dialog.dismiss(); openCollectionScreen(libraryMode)
        }.showThemed()
    }
    private fun cycleCoverLayout() {
        val layouts = availableCoverLayouts()
        coverLayout = layouts[(layouts.indexOf(coverLayout).coerceAtLeast(0) + 1) % layouts.size]
        getSharedPreferences("prefs", 0).edit().putString("cover_layout", coverLayout).apply()
        openCollectionScreen(libraryMode)
        showCornerNotification("Game layout · $coverLayout")
    }
    private fun showGameSortPicker() {
        val options = arrayOf("Recently added", "Title A–Z", "Title Z–A", "Region")
        AlertDialog.Builder(this).setTitle("Sort games").setSingleChoiceItems(options, options.indexOf(gameSortMode).coerceAtLeast(0)) { dialog, which ->
            gameSortMode = options[which]; getSharedPreferences("prefs", 0).edit().putString("game_sort", gameSortMode).apply(); dialog.dismiss(); openCollectionScreen(libraryMode)
        }.setNegativeButton("Cancel", null).showThemed()
    }
    private fun showCheatSortPicker() {
        val options = arrayOf("Name A–Z", "Name Z–A", "Category", "Code lines low to high", "Code lines high to low")
        AlertDialog.Builder(this).setTitle("Sort mods").setSingleChoiceItems(options, options.indexOf(cheatSortMode).coerceAtLeast(0)) { dialog, which ->
            cheatSortMode = options[which]; getSharedPreferences("prefs", 0).edit().putString("cheat_sort", cheatSortMode).apply(); dialog.dismiss(); renderResults()
        }.setNegativeButton("Cancel", null).showThemed()
    }
    private fun buildControllerSettings(container: LinearLayout) {
        container.addView(label("CONTROLLER NAVIGATION"))
        container.addView(label("Use a connected gamepad's D-pad to move focus and its confirm/back buttons to navigate the app."))
        arrayOf("Switch", "PlayStation", "Xbox").forEach { style -> container.addView(button((if (controllerStyle == style) "✓  " else "   ") + style) {
            controllerStyle = style; getSharedPreferences("prefs", 0).edit().putString("controller_style", style).apply(); showSettingsScreen()
        }, LinearLayout.LayoutParams(-1, 48)) }
        container.addView(label("CURRENT SCHEME SHORTCUTS"))
        container.addView(controllerFooter("settings"))
    }
    override fun dispatchKeyEvent(event: KeyEvent): Boolean {
        if (event.action != KeyEvent.ACTION_DOWN) return super.dispatchKeyEvent(event)
        when (event.keyCode) {
            KeyEvent.KEYCODE_DPAD_UP, KeyEvent.KEYCODE_DPAD_DOWN, KeyEvent.KEYCODE_DPAD_LEFT, KeyEvent.KEYCODE_DPAD_RIGHT -> {
                val direction = when (event.keyCode) { KeyEvent.KEYCODE_DPAD_UP -> View.FOCUS_UP; KeyEvent.KEYCODE_DPAD_DOWN -> View.FOCUS_DOWN; KeyEvent.KEYCODE_DPAD_LEFT -> View.FOCUS_LEFT; else -> View.FOCUS_RIGHT }
                currentFocus?.focusSearch(direction)?.let { if (it.requestFocus()) return true }
            }
            KeyEvent.KEYCODE_ENTER, KeyEvent.KEYCODE_DPAD_CENTER, KeyEvent.KEYCODE_BUTTON_A -> { currentFocus?.performClick()?.let { return true } }
            KeyEvent.KEYCODE_BUTTON_B, KeyEvent.KEYCODE_BACK, KeyEvent.KEYCODE_ESCAPE -> { onBackPressed(); return true }
            KeyEvent.KEYCODE_BUTTON_X -> { if (currentScreen == "mods") { showFilterPicker(); return true } }
            KeyEvent.KEYCODE_BUTTON_Y -> { if (currentScreen == "mods") showCheatSortPicker() else if (currentScreen in setOf("games", "recent", "favorites")) showGameSortPicker() else if (currentScreen == "search") openGamesScreen(); return true }
            KeyEvent.KEYCODE_BUTTON_L2 -> { if (currentScreen in setOf("games", "recent", "favorites")) { cycleCoverLayout(); return true } }
            KeyEvent.KEYCODE_BUTTON_R1 -> { if (currentScreen != "settings") toggleQuickFavorite(); return true }
            KeyEvent.KEYCODE_BUTTON_START -> { if (currentScreen == "settings") returnToSearch() else showSettingsScreen(); return true }
        }
        return super.dispatchKeyEvent(event)
    }

    private fun showFirstRunTour(index: Int = 0) {
        if (index !in 0..4) return
        pendingTourDialog?.dismiss()
        tutorialImportChoice = getSharedPreferences("prefs", 0).getString("preferred_game_import", "single") ?: "single"
        val prefs = getSharedPreferences("prefs", 0)
        val page = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(dp(18), dp(14), dp(18), dp(12)); setBackgroundColor(colors[0]) }
        val header = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL; setPadding(dp(12), dp(8), dp(12), dp(8)); background = surface(colors[3], colors[4]) }
        header.addView(TextView(this).apply { text = "PSP CHEAT DB MANAGER"; textSize = 20f; setTextColor(colors[2]); typeface = Typeface.create("sans-serif-condensed", Typeface.BOLD) }, LinearLayout.LayoutParams(0, dp(48), 1f))
        header.addView(TextView(this).apply { text = "${index + 1} / 5"; textSize = 15f; setTextColor(colors[4]); gravity = Gravity.CENTER })
        page.addView(header)
        val progress = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; setPadding(0, dp(9), 0, dp(5)) }
        repeat(5) { n -> progress.addView(View(this).apply { setBackgroundColor(if (n <= index) colors[4] else colors[3]) }, LinearLayout.LayoutParams(0, dp(4), 1f).apply { marginEnd = dp(4) }) }
        page.addView(progress)
        val heading = arrayOf("Set up PPSSPP first", "Choose your PSP game folder", "Choose how you add games", "Optional cover-art key", "Choose cheat sources")
        page.addView(TextView(this).apply { text = heading[index]; textSize = 26f; setTextColor(colors[2]); typeface = Typeface.create("sans-serif-condensed", Typeface.BOLD); setPadding(dp(8), dp(8), dp(8), dp(8)) })
        val body = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(dp(12), dp(12), dp(12), dp(12)); background = surface(colors[1], colors[4]) }
        var keyInput: EditText? = null
        var steamFallback: CheckBox? = null
        when (index) {
            0 -> {
                body.addView(tourText("This independent utility prepares cheat files for the Cheats feature in PPSSPP. We are not affiliated with PPSSPP or its developers. PPSSPP is strongly recommended: install it, then enable Cheats in Settings → System before using exported codes."))
                body.addView(tourText("During PPSSPP setup, choose an easy-to-find storage location for its PSP data when offered (for example, a folder you can browse in your file manager). Android may hide app-managed default locations behind its storage manager, making cheat files harder to place."))
                body.addView(tourAction("DOWNLOAD PPSSPP · OFFICIAL WEBSITE") { openPpssppDownloads() })
                body.addView(tourText("For an individual game, export its selected mods or all its mods as a game-ID .ini file (for example, ULUS12345.ini). Put that .ini in PPSSPP’s PSP/Cheats folder, then open that same game in PPSSPP and choose Cheats. This slide explains individual game .ini files."))
            }
            1 -> {
                body.addView(tourText("Choose the folder where you keep your PSP ISO, PBP, or CHD game files. Android will grant this app access only to the folder you select here; it does not request broad device-storage access."))
                tutorialFolderLabel = tourText(gameFolderText())
                body.addView(tutorialFolderLabel)
                body.addView(tourAction("CHOOSE PSP GAME FOLDER") { chooseGameFolder() })
                body.addView(tourText("You can also skip this and choose individual files later. Your selection is remembered on this device."))
            }
            2 -> {
                body.addView(tourText("When you press Add PSP Game, choose one file or scan the whole selected folder and its subfolders. A full scan can take several minutes for a large library and continues in the background; the app looks for cover art as games are found."))
                val choices = RadioGroup(this).apply { orientation = RadioGroup.VERTICAL }
                val one = RadioButton(this).apply { text = "Single item · choose one ISO / PBP / CHD"; setTextColor(colors[2]); buttonTintList = android.content.res.ColorStateList.valueOf(colors[4]); isChecked = tutorialImportChoice == "single" }
                val whole = RadioButton(this).apply { text = "Whole folder · scan nested game files"; setTextColor(colors[2]); buttonTintList = android.content.res.ColorStateList.valueOf(colors[4]); isChecked = tutorialImportChoice == "folder" }
                choices.addView(one); choices.addView(whole)
                choices.setOnCheckedChangeListener { _, checked -> tutorialImportChoice = if (checked == whole.id) "folder" else "single" }
                // Assign stable IDs so the selected radio item can be identified reliably.
                one.id = View.generateViewId(); whole.id = View.generateViewId(); one.isChecked = tutorialImportChoice == "single"
                body.addView(choices)
                body.addView(tourText("This choice only changes which option is shown first. Add PSP Game will always let you switch modes."))
            }
            3 -> {
                body.addView(tourText("Optional: add your own SteamGridDB API key to try its box-art service when the free Libretro lookup has no match. This is not your Steam password. It is encrypted with Android Keystore and stays on this device. Leave it blank to skip."))
                keyInput = edit("SteamGridDB API key").apply { inputType = InputType.TYPE_CLASS_TEXT or InputType.TYPE_TEXT_VARIATION_PASSWORD; importantForAutofill = View.IMPORTANT_FOR_AUTOFILL_NO; setSingleLine(true) }
                body.addView(keyInput)
                body.addView(TextView(this).apply { text = if (getSteamGridApiKey().isNullOrBlank()) "No key saved" else "A key is already saved securely. Leave blank to keep it."; textSize = 13f; setTextColor(colors[4]); setPadding(0, dp(4), 0, dp(8)) })
                steamFallback = CheckBox(this).apply { text = "Enable SteamGridDB as an optional fallback"; setTextColor(colors[2]); buttonTintList = android.content.res.ColorStateList.valueOf(colors[4]); isChecked = prefs.getBoolean("steamgrid_cover_enabled", false) }
                body.addView(steamFallback)
                body.addView(tourAction("OPEN STEAMGRIDDB API KEY PAGE") { try { startActivity(Intent(Intent.ACTION_VIEW, Uri.parse("https://www.steamgriddb.com/profile/preferences"))) } catch (_: Exception) { Toast.makeText(this, "Could not open the SteamGridDB key page.", Toast.LENGTH_SHORT).show() } })
            }
            4 -> {
                body.addView(tourText("Sources contain community-made cheat data. Review source details and only install sources you trust. Downloads require your confirmation, are fetched over HTTPS, and imported archive sizes are limited. Imported cheats are unverified."))
                val sources = listOf(
                    Triple("\"CWCheat Database Plus\" · Saramagrean · RECOMMENDED", "https://github.com/Saramagrean/CWCheat-Database-Plus-/archive/refs/heads/master.zip", "CWCheat Database Plus — Saramagrean"),
                    Triple("PPSSPP workarounds · LunaMoo", "https://github.com/LunaMoo/PPSSPP_workarounds/archive/refs/heads/master.zip", "PPSSPP workarounds — LunaMoo")
                )
                sources.forEachIndexed { sourceIndex, (label, url, name) ->
                    val card = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(dp(8), dp(4), dp(8), dp(4)); background = surface(colors[3], colors[4]) }
                    card.addView(TextView(this).apply { text = label; textSize = 14f; setTextColor(if (sourceIndex == 0) colors[4] else colors[2]); typeface = Typeface.create("sans-serif-condensed", Typeface.BOLD) })
                    card.addView(TextView(this).apply { text = url; textSize = 10f; setTextColor(colors[4]); maxLines = 2; ellipsize = TextUtils.TruncateAt.MIDDLE; setOnClickListener { try { startActivity(Intent(Intent.ACTION_VIEW, Uri.parse(url))) } catch (_: Exception) { } } })
                    val row = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL }
                    row.addView(CheckBox(this).apply { text = "Enabled"; setTextColor(colors[2]); buttonTintList = android.content.res.ColorStateList.valueOf(colors[4]); isChecked = sourceIsEnabled(name); setOnCheckedChangeListener { _, on -> setSourceEnabled(name, on) } }, LinearLayout.LayoutParams(0, dp(38), 1f))
                    row.addView(button("UPDATE / INSTALL") { confirmAndDownload(url, name) })
                    card.addView(row); body.addView(card)
                }
                body.addView(tourText("You can add another HTTPS cheat-source link later in Settings → Sources. Enabling a source does not download it."))
            }
        }
        val scroll = ScrollView(this).apply { isFillViewport = false; addView(body) }
        page.addView(scroll, LinearLayout.LayoutParams(-1, 0, 1f).apply { topMargin = dp(4); bottomMargin = dp(8) })
        val footer = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL; setPadding(0, dp(4), 0, 0) }
        val skip = button("SKIP") { finishTutorial() }
        footer.addView(skip, LinearLayout.LayoutParams(dp(76), dp(48)))
        footer.addView(button("‹ BACK") { if (index > 0) showFirstRunTour(index - 1) else finishTutorial() }, LinearLayout.LayoutParams(0, dp(48), 1f).apply { marginStart = dp(6) })
        footer.addView(button(if (index == 4) "FINISH" else "NEXT  ›") {
            if (index == 2) prefs.edit().putString("preferred_game_import", tutorialImportChoice).apply()
            if (index == 3) {
                prefs.edit().putBoolean("steamgrid_cover_enabled", steamFallback?.isChecked == true).apply()
                val key = keyInput?.text?.toString()?.trim().orEmpty()
                if (key.isNotEmpty()) try { saveSteamGridApiKey(key) } catch (_: Exception) { Toast.makeText(this, "Could not securely save that API key; it was not stored.", Toast.LENGTH_LONG).show() }
                keyInput?.text?.clear()
            }
            if (index < 4) showFirstRunTour(index + 1) else finishTutorial()
        }, LinearLayout.LayoutParams(0, dp(48), 1f).apply { marginStart = dp(6) })
        page.addView(footer)
        val dialog = AlertDialog.Builder(this).setView(page).create()
        dialog.setCancelable(false)
        dialog.setOnShowListener {
            dialog.window?.setLayout(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT)
            dialog.window?.setBackgroundDrawableResource(android.R.color.transparent)
        }
        pendingTourDialog = dialog
        dialog.show()
        dialog.window?.setLayout(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT)
    }

    private fun tourText(value: String): TextView = TextView(this).apply {
        text = value; textSize = 16f; setTextColor(colors[2]); typeface = Typeface.create("sans-serif-condensed", Typeface.NORMAL); setPadding(dp(8), dp(8), dp(8), dp(10)); setLineSpacing(dp(2).toFloat(), 1f)
    }
    private fun tourAction(value: String, action: () -> Unit): Button = button(value, action).apply { isAllCaps = false; textSize = 14f; setPadding(dp(10), dp(5), dp(10), dp(5)) }
    private fun finishTutorial() {
        getSharedPreferences("prefs", 0).edit().putBoolean("setup_tour_complete", true).apply()
        pendingTourDialog?.dismiss(); pendingTourDialog = null; tutorialFolderLabel = null
    }

    private fun openPpssppDownloads() {
        try { startActivity(Intent(Intent.ACTION_VIEW, Uri.parse("https://www.ppsspp.org/download/"))) }
        catch (_: Exception) { Toast.makeText(this, "Could not open the PPSSPP download page.", Toast.LENGTH_SHORT).show() }
    }

    private fun exportFolderText(): String {
        val saved = getSharedPreferences("prefs", 0).getString(EXPORT_TREE_PREF, null) ?: return "No export folder chosen yet. Choose one once; it will be remembered."
        val uri = Uri.parse(saved)
        val name = uri.lastPathSegment.orEmpty().substringAfterLast(':').substringAfterLast('/').ifBlank { "Selected folder" }
        return "Remembered export folder: $name"
    }

    private fun chooseExportFolder() {
        val intent = Intent(Intent.ACTION_OPEN_DOCUMENT_TREE)
        getSharedPreferences("prefs", 0).getString(EXPORT_TREE_PREF, null)?.let { saved ->
            if (android.os.Build.VERSION.SDK_INT >= 26) intent.putExtra(DocumentsContract.EXTRA_INITIAL_URI, Uri.parse(saved))
        }
        try { startActivityForResult(intent, REQ_EXPORT_FOLDER) }
        catch (e: Exception) { status.text = "Could not open the folder picker: ${e.message ?: "No file picker is available"}" }
    }

    private fun scanPpssppCheatFolder(showNotice: Boolean = true) {
        if (installedIniScanInProgress) return
        val saved = getSharedPreferences("prefs", 0).getString(EXPORT_TREE_PREF, null)
        if (saved.isNullOrBlank()) {
            if (::status.isInitialized) status.text = "Choose PPSSPP's PSP/Cheats folder before scanning its INI files."
            return
        }
        installedIniScanInProgress = true
        installedIniScanComplete = false
        installedIniSummary = "Scanning PPSSPP game INI files…"
        if (currentScreen == "settings") showSettingsScreen()
        worker.execute {
            try {
                val tree = Uri.parse(saved)
                val files = listPpssppIniFiles(tree)
                val fingerprint = fingerprintPpssppIniFiles(files)

                val scannedGames = linkedMapOf<String, InstalledIniStats>()
                var scannedFiles = 0
                var skippedFiles = 0
                var totalBytes = 0
                for ((fileIndex, file) in files.withIndex()) {
                    if (totalBytes >= MAX_EXISTING_INI_TOTAL_BYTES) { skippedFiles += files.size - fileIndex; break }
                    try {
                        val fileUri = DocumentsContract.buildDocumentUriUsingTree(tree, file.documentId)
                        val bytes = contentResolver.openInputStream(fileUri)?.use { readLimited(it, MAX_EXISTING_INI_FILE_BYTES) }
                            ?: throw IllegalStateException("File could not be opened")
                        if (totalBytes + bytes.size > MAX_EXISTING_INI_TOTAL_BYTES) { skippedFiles++; continue }
                        totalBytes += bytes.size
                        val idsInFile = parseInstalledIni(bytes.toString(Charsets.UTF_8), file.name, scannedGames)
                        idsInFile.forEach { id -> scannedGames.getOrPut(id) { InstalledIniStats() }.files++ }
                        scannedFiles++
                    } catch (_: Exception) { skippedFiles++ }
                }
                runOnUiThread {
                    installedIniScanInProgress = false
                    installedIniStats.clear(); installedIniStats.putAll(scannedGames)
                    installedIniFingerprint = fingerprint
                    installedIniFingerprintInitialized = true
                    installedIniScanComplete = true
                    val modCount = scannedGames.values.sumOf { it.mods }
                    val enabledCount = scannedGames.values.sumOf { it.enabled }
                    val disabledCount = (modCount - enabledCount).coerceAtLeast(0)
                    installedIniSummary = if (scannedFiles == 0) "No readable game .ini files found in the selected folder."
                    else "$scannedFiles INI files · $enabledCount enabled · $disabledCount disabled · ${scannedGames.size} games" + if (skippedFiles > 0) " · $skippedFiles skipped by file or size limits" else ""
                    refreshInstalledIniViews()
                    if (showNotice) showCornerNotification(if (scannedFiles == 0) "No game INI files found" else "Scanned $scannedFiles INI files · $enabledCount enabled mods")
                }
            } catch (e: Exception) {
                runOnUiThread {
                    installedIniScanInProgress = false
                    installedIniStats.clear(); installedIniScanComplete = false
                    installedIniFingerprintInitialized = false
                    installedIniSummary = "Could not scan this folder. Choose the PPSSPP PSP/Cheats folder again if its access changed."
                    refreshInstalledIniViews()
                    if (showNotice) showCornerNotification("PPSSPP INI scan failed: ${e.message ?: "folder access error"}", true)
                }
            }
        }
    }

    private fun listPpssppIniFiles(tree: Uri): List<IniFileRef> {
        val rootId = DocumentsContract.getTreeDocumentId(tree)
        val childrenUri = DocumentsContract.buildChildDocumentsUriUsingTree(tree, rootId)
        val files = mutableListOf<IniFileRef>()
        contentResolver.query(childrenUri, arrayOf(
            DocumentsContract.Document.COLUMN_DOCUMENT_ID,
            DocumentsContract.Document.COLUMN_DISPLAY_NAME,
            DocumentsContract.Document.COLUMN_SIZE,
            DocumentsContract.Document.COLUMN_LAST_MODIFIED
        ), null, null, null)?.use { cursor ->
            val idColumn = cursor.getColumnIndexOrThrow(DocumentsContract.Document.COLUMN_DOCUMENT_ID)
            val nameColumn = cursor.getColumnIndexOrThrow(DocumentsContract.Document.COLUMN_DISPLAY_NAME)
            val sizeColumn = cursor.getColumnIndex(DocumentsContract.Document.COLUMN_SIZE)
            val modifiedColumn = cursor.getColumnIndex(DocumentsContract.Document.COLUMN_LAST_MODIFIED)
            while (cursor.moveToNext() && files.size < MAX_EXISTING_INI_FILES) {
                val name = cursor.getString(nameColumn) ?: continue
                if (!name.endsWith(".ini", ignoreCase = true)) continue
                val size = if (sizeColumn >= 0 && !cursor.isNull(sizeColumn)) cursor.getLong(sizeColumn) else -1L
                val modified = if (modifiedColumn >= 0 && !cursor.isNull(modifiedColumn)) cursor.getLong(modifiedColumn) else -1L
                files.add(IniFileRef(cursor.getString(idColumn), name, size, modified))
            }
        } ?: error("Android could not list the selected folder.")
        return files.sortedBy { it.documentId }
    }

    private fun fingerprintPpssppIniFiles(files: List<IniFileRef>): String = files.joinToString("\n") {
        "${it.documentId}|${it.name}|${it.size}|${it.lastModified}"
    }

    private fun startPpssppIniMonitoring() {
        if (iniMonitorActive) return
        val saved = getSharedPreferences("prefs", 0).getString(EXPORT_TREE_PREF, null) ?: return
        iniMonitorActive = true
        val tree = Uri.parse(saved)
        val rootId = DocumentsContract.getTreeDocumentId(tree)
        val childrenUri = DocumentsContract.buildChildDocumentsUriUsingTree(tree, rootId)
        if (iniObservedChildrenUri != childrenUri) {
            iniContentObserver?.let { observer -> try { contentResolver.unregisterContentObserver(observer) } catch (_: Exception) { } }
            iniContentObserver = object : ContentObserver(iniMonitorHandler) {
                override fun onChange(selfChange: Boolean) { schedulePpssppIniRescan() }
                override fun onChange(selfChange: Boolean, uri: Uri?) { schedulePpssppIniRescan() }
            }
            iniObservedChildrenUri = childrenUri
            try { contentResolver.registerContentObserver(childrenUri, true, iniContentObserver!!) } catch (_: Exception) { /* metadata polling remains active */ }
        }
        val poll = object : Runnable {
            override fun run() {
                if (!iniMonitorActive) return
                checkPpssppIniFingerprint()
                iniMonitorHandler.postDelayed(this, INI_FOLDER_POLL_MS)
            }
        }
        iniPollRunnable = poll
        iniMonitorHandler.postDelayed(poll, INI_FOLDER_POLL_MS)
        scanPpssppCheatFolder(showNotice = false)
    }

    private fun stopPpssppIniMonitoring() {
        iniMonitorActive = false
        iniPollRunnable?.let(iniMonitorHandler::removeCallbacks)
        iniPollRunnable = null
        iniRescanRunnable?.let(iniMonitorHandler::removeCallbacks)
        iniRescanRunnable = null
        iniContentObserver?.let { observer -> try { contentResolver.unregisterContentObserver(observer) } catch (_: Exception) { } }
        iniContentObserver = null
        iniObservedChildrenUri = null
    }

    private fun schedulePpssppIniRescan(delayMs: Long = INI_CHANGE_DEBOUNCE_MS) {
        iniRescanRunnable?.let(iniMonitorHandler::removeCallbacks)
        val rescan = Runnable { scanPpssppCheatFolder(showNotice = false) }
        iniRescanRunnable = rescan
        iniMonitorHandler.postDelayed(rescan, delayMs)
    }

    private fun checkPpssppIniFingerprint() {
        if (iniFingerprintCheckInFlight || installedIniScanInProgress) return
        val saved = getSharedPreferences("prefs", 0).getString(EXPORT_TREE_PREF, null) ?: return
        val oldFingerprint = installedIniFingerprint
        val hasFingerprint = installedIniFingerprintInitialized
        iniFingerprintCheckInFlight = true
        worker.execute {
            var changed = false
            try {
                val fingerprint = fingerprintPpssppIniFiles(listPpssppIniFiles(Uri.parse(saved)))
                changed = hasFingerprint && fingerprint != oldFingerprint
            } catch (_: Exception) { /* Resume and explicit scans will report lost access. */ }
            runOnUiThread {
                iniFingerprintCheckInFlight = false
                if (changed) schedulePpssppIniRescan()
            }
        }
    }

    private fun parseInstalledIni(text: String, fileName: String, counts: MutableMap<String, InstalledIniStats>): Set<String> {
        val fallbackId = SERIAL_PATTERN.find(fileName.uppercase(Locale.ROOT))?.let { it.groupValues[1] + it.groupValues[2] }
        var gameId = fallbackId
        val gamesInFile = linkedSetOf<String>()
        var currentModEnabled: Boolean? = null
        var codeLines = 0
        fun finishMod() {
            val id = gameId
            val enabled = currentModEnabled
            if (id != null && enabled != null && codeLines > 0) {
                val stats = counts.getOrPut(id) { InstalledIniStats() }
                stats.mods++
                if (enabled) stats.enabled++
            }
            currentModEnabled = null; codeLines = 0
        }
        for (rawLine in text.lineSequence()) {
            val line = rawLine.trim()
            when {
                line.startsWith("_S ", true) -> {
                    finishMod()
                    val match = SERIAL_PATTERN.find(line.uppercase(Locale.ROOT))
                    gameId = match?.let { it.groupValues[1] + it.groupValues[2] } ?: fallbackId
                    gameId?.let(gamesInFile::add)
                }
                line.startsWith("_C0 ", true) || line.startsWith("_C1 ", true) -> {
                    finishMod()
                    currentModEnabled = line.startsWith("_C1 ", true)
                }
                line.startsWith("_L ", true) && currentModEnabled != null -> codeLines++
            }
        }
        finishMod()
        if (gamesInFile.isEmpty()) fallbackId?.let(gamesInFile::add)
        return gamesInFile
    }

    private fun installedIniLine(id: String): String? {
        val stats = installedIniStats[id] ?: return if (installedIniScanComplete) "PPSSPP INI · no mod codes found" else null
        return "PPSSPP INI · ${stats.enabled} enabled · ${(stats.mods - stats.enabled).coerceAtLeast(0)} disabled"
    }

    private fun refreshInstalledIniViews() {
        when (currentScreen) {
            "settings" -> showSettingsScreen()
            "mods" -> if (currentGameId.isNotBlank()) openModsScreen(currentGameId)
            "games", "recent", "favorites" -> openCollectionScreen(currentScreen)
            else -> if (::status.isInitialized) status.text = installedIniSummary
        }
    }

    private fun saveExportToRememberedFolder(fileName: String, contents: String) {
        val pref = getSharedPreferences("prefs", 0)
        val saved = pref.getString(EXPORT_TREE_PREF, null)
        if (saved == null) {
            pendingExport = fileName to contents
            status.text = "Choose an export folder once. The app will remember it and save this file there."
            chooseExportFolder()
            return
        }
        try {
            val tree = Uri.parse(saved)
            val rootId = DocumentsContract.getTreeDocumentId(tree)
            val rootDocument = DocumentsContract.buildDocumentUriUsingTree(tree, rootId)
            val children = DocumentsContract.buildChildDocumentsUriUsingTree(tree, rootId)
            var oldDocument: Uri? = null
            contentResolver.query(children, arrayOf(DocumentsContract.Document.COLUMN_DOCUMENT_ID, DocumentsContract.Document.COLUMN_DISPLAY_NAME), null, null, null)?.use { cursor ->
                val idColumn = cursor.getColumnIndexOrThrow(DocumentsContract.Document.COLUMN_DOCUMENT_ID)
                val nameColumn = cursor.getColumnIndexOrThrow(DocumentsContract.Document.COLUMN_DISPLAY_NAME)
                while (cursor.moveToNext()) if (cursor.getString(nameColumn) == fileName) {
                    oldDocument = DocumentsContract.buildDocumentUriUsingTree(tree, cursor.getString(idColumn)); break
                }
            }
            var previousDbBackupName: String? = null
            if (fileName.equals("cheat.db", true) && oldDocument != null) {
                val previousBytes = contentResolver.openInputStream(oldDocument!!)?.use { readLimited(it, 96 * 1024 * 1024) }
                    ?: error("Could not read the existing cheat.db; it was left untouched.")
                val backupName = "cheat.db.backup-${System.currentTimeMillis()}"
                val backupUri = DocumentsContract.createDocument(contentResolver, rootDocument, "application/octet-stream", backupName)
                    ?: error("Could not make a backup of the existing cheat.db; it was left untouched.")
                try {
                    contentResolver.openOutputStream(backupUri, "wt")!!.use { it.write(previousBytes) }
                    val verifiedBackup = contentResolver.openInputStream(backupUri)?.use { readLimited(it, 96 * 1024 * 1024) }
                    if (verifiedBackup == null || !previousBytes.contentEquals(verifiedBackup)) error("The existing cheat.db backup could not be verified; the original database was left untouched.")
                    previousDbBackupName = backupName
                } catch (error: Exception) {
                    try { DocumentsContract.deleteDocument(contentResolver, backupUri) } catch (_: Exception) { }
                    throw error
                }
            }
            oldDocument?.let { DocumentsContract.deleteDocument(contentResolver, it) }
            val created = DocumentsContract.createDocument(contentResolver, rootDocument, "application/octet-stream", fileName)
                ?: error("The selected folder did not create a file")
            contentResolver.openOutputStream(created, "wt")!!.bufferedWriter(Charsets.UTF_8).use { it.write(contents) }
            var actualUri = created
            val actualName = contentResolver.query(created, arrayOf(DocumentsContract.Document.COLUMN_DISPLAY_NAME), null, null, null)?.use { cursor ->
                if (cursor.moveToFirst()) cursor.getString(cursor.getColumnIndexOrThrow(DocumentsContract.Document.COLUMN_DISPLAY_NAME)) else null
            }
            if (actualName != null && actualName != fileName) {
                actualUri = try { DocumentsContract.renameDocument(contentResolver, created, fileName) } catch (_: Exception) { null }
                    ?: run { DocumentsContract.deleteDocument(contentResolver, created); error("The file provider tried to change the filename to $actualName and would not keep $fileName") }
            }
            val finalName = contentResolver.query(actualUri, arrayOf(DocumentsContract.Document.COLUMN_DISPLAY_NAME), null, null, null)?.use { cursor ->
                if (cursor.moveToFirst()) cursor.getString(cursor.getColumnIndexOrThrow(DocumentsContract.Document.COLUMN_DISPLAY_NAME)) else fileName
            } ?: fileName
            if (finalName != fileName) { DocumentsContract.deleteDocument(contentResolver, actualUri); error("The export location added an unwanted extension. The file was removed instead of saving it as $finalName") }
            val modCount = Regex("(?m)^_C[01] ").findAll(contents).count()
            val codeCount = Regex("(?m)^_L ").findAll(contents).count()
            val message = "Export complete: $finalName\n$modCount mod(s) · $codeCount code lines\nFolder: ${shortExportFolder()}"
            status.text = message
            showCornerNotification("Export complete · $finalName")
            if (fileName.endsWith(".ini", ignoreCase = true)) schedulePpssppIniRescan(500)
            if (fileName.equals("cheat.db", true)) {
                val mergeNotice = if (previousDbBackupName != null) "Existing database entries were merged and duplicate cheats were skipped. A copy of the previous file is saved as $previousDbBackupName." else "No existing cheat.db was found, so this is a new database file."
                AlertDialog.Builder(this).setTitle("PPSSPP database ready")
                    .setMessage("$mergeNotice\n\nSaved cheat.db to ${shortExportFolder()}. In PPSSPP, open this game, open the pause menu → Cheats → Import from cheat.db, then enable the imported mod. Also make sure Cheats are enabled in PPSSPP's settings.\n\nFor the automatic import option, the selected folder must be PPSSPP's PSP/Cheats folder. If your PPSSPP uses a different storage folder, choose that PSP/Cheats folder here.")
                    .setPositiveButton("OK", null).showThemed()
            }
        } catch (e: SecurityException) {
            pref.edit().remove(EXPORT_TREE_PREF).apply()
            exportFolderLabel.text = exportFolderText()
            pendingExport = fileName to contents
            status.text = "The saved export folder is no longer available. Choose it again to save this file."
            showCornerNotification("Export folder unavailable", isError = true)
            chooseExportFolder()
        } catch (e: Exception) {
            status.text = "Could not save in the remembered folder: ${e.message ?: e.javaClass.simpleName}. Choose a different export folder."
        }
    }

    private fun button(text: String, action: () -> Unit) = Button(this).apply { this.text = text; isAllCaps = false; textSize = if (compactLandscape()) 11f else 13f; typeface = Typeface.create("sans-serif-condensed", Typeface.NORMAL); setTextColor(colors[2]); background = surface(blend(colors[1], colors[4], 0.10f), colors[4]); setPadding(dp(4), dp(3), dp(4), dp(3)); setMinHeight(0); minimumHeight = 0; setOnClickListener { action() } }
    private fun blend(base: Int, tint: Int, fraction: Float): Int {
        val f = fraction.coerceIn(0f, 1f)
        return Color.rgb(
            (Color.red(base) * (1f - f) + Color.red(tint) * f).toInt(),
            (Color.green(base) * (1f - f) + Color.green(tint) * f).toInt(),
            (Color.blue(base) * (1f - f) + Color.blue(tint) * f).toInt()
        )
    }
    private fun label(text: String) = TextView(this).apply { this.text = text; setTextColor(colors[2]); textSize = 14f; typeface = Typeface.create("sans-serif-condensed", Typeface.NORMAL); setPadding(4, 8, 4, 8) }
    private fun edit(hintText: String) = EditText(this).apply { hint = hintText; setHintTextColor(colors[4]); setTextColor(colors[2]); textSize = if (compactLandscape()) 12f else 14f; typeface = Typeface.create("sans-serif-condensed", Typeface.NORMAL); setSingleLine(true); background = surface(colors[3], colors[4]); setPadding(dp(10), dp(5), dp(10), dp(5)) }
    private fun compactLandscape(): Boolean {
        val config = resources.configuration
        val displayRatio = resources.displayMetrics.widthPixels.toFloat() / resources.displayMetrics.heightPixels.coerceAtLeast(1)
        // Compact controls fit 4:3 and narrow windows; 16:9 landscape keeps the full labels.
        return config.screenHeightDp <= 520 || displayRatio <= 1.55f
    }
    private fun recolor(v: View) { v.setBackgroundColor(if (v is LinearLayout || v is ScrollView) colors[0] else if (v is EditText) colors[3] else colors[1]); if (v is TextView) v.setTextColor(colors[2]); if (v is ViewGroup) for (i in 0 until v.childCount) recolor(v.getChildAt(i)) }
    private fun showHelp() { showFirstRunTour() }
    private fun showWelcomeIfNeeded() { val p = getSharedPreferences("prefs", 0); theme = migrateTheme(p.getString("theme", "Ghost Protocol") ?: "Ghost Protocol"); colors = palette(theme); p.edit().putString("theme", theme).apply(); if (!p.getBoolean("setup_tour_complete", false)) showFirstRunTour() }

    private fun loadTitleCatalog() {
        catalogStatus.text = "Loading saved PSP title catalog…"
        worker.execute {
            val cached = try { openFileInput(TITLE_CATALOG_FILE).bufferedReader().use { it.readText() } } catch (_: Exception) { null }
            val parsed = cached?.let { parseTitleCatalog(it) }.orEmpty()
            if (parsed.isNotEmpty()) runOnUiThread { setTitleCatalog(parsed, "${parsed.size} PSP game IDs loaded. Type to filter.") }
            else runOnUiThread { fetchTitleCatalog(false) }
        }
    }

    private fun fetchTitleCatalog(showErrors: Boolean) {
        if (::catalogStatus.isInitialized) catalogStatus.text = "Downloading PSP title names and IDs…"
        worker.execute {
            try {
                val connection = URL(TITLE_CATALOG_URL).openConnection() as HttpURLConnection
                connection.connectTimeout = 20000; connection.readTimeout = 45000; connection.setRequestProperty("User-Agent", "PSP-Cheat-DB-Manager-Android/0.1")
                val csv = connection.inputStream.use { readLimited(it, MAX_CATALOG_BYTES).toString(Charsets.UTF_8).removePrefix("\uFEFF") }
                connection.disconnect()
                val entries = parseTitleCatalog(csv)
                if (entries.isEmpty()) error("The PSP title list had no usable game entries")
                openFileOutput(TITLE_CATALOG_FILE, MODE_PRIVATE).use { it.write(csv.toByteArray(Charsets.UTF_8)) }
                runOnUiThread { setTitleCatalog(entries, "${entries.size} PSP game IDs loaded. Type to filter.") }
            } catch (e: Exception) {
                runOnUiThread {
                    catalogStatus.text = "Title list unavailable. Enter the game ID manually or try Load titles again."
                    if (showErrors) AlertDialog.Builder(this).setTitle("Could not load PSP game list").setMessage(e.message ?: "Check your internet connection and retry.").setPositiveButton("OK", null).showThemed()
                }
            }
        }
    }

    private fun setTitleCatalog(entries: List<GameTitle>, message: String) {
        if (entries !== titleCatalog) { titleCatalog.clear(); titleCatalog.addAll(entries) }
        title.setAdapter(TitleAdapter(titleCatalog))
        catalogStatus.text = message
        if (currentScreen == "mods" && ::coverImageView.isInitialized) {
            val match = titleCatalog.firstOrNull { it.id == currentGameId }
            if (match != null) loadCoverArt(match.id, match.title, match.region)
        }
    }

    private fun parseTitleCatalog(csv: String): List<GameTitle> {
        val lines = csv.lineSequence().iterator(); if (!lines.hasNext()) return emptyList()
        val header = parseCsvLine(lines.next()).mapIndexed { i, s -> s.trim().lowercase(Locale.ROOT) to i }.toMap()
        val systemCol = header["system"] ?: return emptyList(); val categoryCol = header["category"] ?: return emptyList()
        val titleCol = header["title"] ?: return emptyList(); val serialCol = header["serial"] ?: return emptyList(); val regionCol = header["region"]
        val out = linkedMapOf<String, GameTitle>()
        while (lines.hasNext()) {
            val fields = parseCsvLine(lines.next()); val maxCol = maxOf(systemCol, categoryCol, titleCol, serialCol)
            if (fields.size <= maxCol || fields[systemCol].trim() != "Sony PlayStation Portable" || fields[categoryCol].trim() != "Games") continue
            val gameTitle = fields[titleCol].trim(); if (gameTitle.isBlank()) continue
            SERIAL_PATTERN.findAll(fields[serialCol].uppercase()).forEach { match ->
                val id = match.groupValues[1] + match.groupValues[2]
                val region = regionCol?.let { fields.getOrNull(it)?.trim().orEmpty() }.orEmpty()
                out.putIfAbsent(id, GameTitle(gameTitle, id, countryName(region)))
            }
        }
        return out.values.sortedBy { it.title.lowercase(Locale.ROOT) }
    }

    private fun parseCsvLine(line: String): List<String> {
        val fields = mutableListOf<String>(); val field = StringBuilder(); var quoted = false; var i = 0
        while (i < line.length) {
            val ch = line[i]
            if (ch == '"') { if (quoted && i + 1 < line.length && line[i + 1] == '"') { field.append('"'); i++ } else quoted = !quoted }
            else if (ch == ',' && !quoted) { fields.add(field.toString()); field.setLength(0) }
            else field.append(ch)
            i++
        }
        fields.add(field.toString()); return fields
    }

    private fun searchCoverArtForSelection(target: ImageView) {
        val id = gameId.text.toString().uppercase().replace(Regex("[-_ ]"), "").trim()
        if (!id.matches(Regex("[A-Z]{4}\\d{5}"))) {
            Toast.makeText(this, "Choose a game or enter its PSP ID first.", Toast.LENGTH_SHORT).show()
            return
        }
        val meta = titleCatalog.firstOrNull { it.id == id }
        val gameTitle = meta?.title ?: db[id]?.title?.takeIf { it.isNotBlank() } ?: title.text.toString().takeIf { it.isNotBlank() } ?: id
        val region = meta?.region ?: ""
        selectedGameFile.text = "$gameTitle\n$id · ${if (region.isBlank()) "PSP GAME" else countryName(region)}\nSEARCHING FOR BOX ART…"
        loadCoverArt(id, gameTitle, region, target, forceSearch = true)
    }

    private fun loadCoverArt(id: String, gameTitle: String, region: String, target: ImageView? = null, forceSearch: Boolean = false) {
        val imageView = target ?: if (::coverImageView.isInitialized) coverImageView else null
        if (imageView == null || gameTitle.isBlank()) return
        val cacheDir = File(filesDir, "psp-covers").apply { mkdirs() }
        val cacheFile = File(cacheDir, "$id.png")
        if (!forceSearch && cacheFile.isFile) {
            BitmapFactory.decodeFile(cacheFile.absolutePath)?.let {
                imageView.setImageBitmap(it)
                if (target == null && ::coverOverlayView.isInitialized) coverOverlayView.text = "${gameTitle.take(28)} · $id\nBOX ART LOADED · TAP TO REFRESH"
                recentCoverStatusViews[id]?.text = "Cover art loaded"
                if (::status.isInitialized && currentGameId == id) status.text = "Cover art loaded · $id"
                return
            }
        }
        imageView.setImageDrawable(null)
        recentCoverStatusViews[id]?.text = "Searching cover art…"
        if (target == null && ::coverOverlayView.isInitialized) coverOverlayView.text = "${gameTitle.take(28)} · $id\nSEARCHING FOR BOX ART…"
        if (!activeCoverSearches.add(id)) return
        if (::status.isInitialized && currentGameId == id) status.text = "Searching box art by game title and region…"
        coverWorker.execute {
            try {
                val base = "https://thumbnails.libretro.com/Sony%20-%20PlayStation%20Portable/Named_Boxarts/"
                val regionSuffix = when (region.lowercase(Locale.ROOT)) {
                    "united states", "usa", "north america" -> "USA"
                    "europe", "eu" -> "Europe"
                    "japan", "jp" -> "Japan"
                    "korea", "south korea" -> "Korea"
                    "australia", "au" -> "Australia"
                    else -> when { id.startsWith("ULUS") || id.startsWith("UCUS") -> "USA"; id.startsWith("ULES") || id.startsWith("UCES") -> "Europe"; id.startsWith("ULJM") || id.startsWith("NPJH") -> "Japan"; else -> "" }
                }
                val technicalTitle = gameTitle
                    .replace(Regex("\\s*[\\[(](?:EU|EUR|EUROPE|USA|US|JP|JPN|JAPAN|WORLD)[\\])]?\\s*$", RegexOption.IGNORE_CASE), "")
                    .replace(Regex("\\s+\\((?:Europe|USA|Japan|World)\\)$", RegexOption.IGNORE_CASE), "").trim()
                val cleanTitle = technicalTitle.replace(Regex("[&*/:<>?\\\\|]"), "_").trim()
                val rawCleanTitle = gameTitle.replace(Regex("[&*/:<>?\\\\|]"), "_").trim()
                val libraryTitles = listOf(technicalTitle, technicalTitle.replace(Regex(":\\s*"), " - ")).distinct()
                val candidates = buildList {
                    add("$id.png")
                    libraryTitles.forEach { libTitle ->
                        if (regionSuffix.isNotBlank()) add("$libTitle ($regionSuffix).png")
                        listOf("USA", "Europe", "Japan", "Korea", "Australia").filter { it != regionSuffix }.forEach { add("$libTitle ($it).png") }
                        if (regionSuffix.equals("Europe", true)) add("$libTitle (Europe) (En,Fr,De,Es,It).png")
                        add("$libTitle.png")
                    }
                    if (rawCleanTitle != cleanTitle) {
                        if (regionSuffix.isNotBlank()) add("$rawCleanTitle ($regionSuffix).png")
                        add("$rawCleanTitle.png")
                    }
                }.distinct()
                // Resolve against the archive's real names first. This avoids case,
                // punctuation, and language-tag mismatches (for example PSP's
                // “God Of War: … [EU]” versus Libretro's “God of War - … (Europe)”).
                var imageBytes: ByteArray? = try { fetchLibretroIndexedCover(technicalTitle, id, region, cacheDir) } catch (_: Exception) { null }
                if (imageBytes == null) {
                    val completion: CompletionService<Pair<String, ByteArray?>> = ExecutorCompletionService(coverProbeWorkers)
                    val probes = mutableListOf<Future<Pair<String, ByteArray?>>>()
                    candidates.forEach { name -> probes.add(completion.submit(Callable {
                        val url = base + URLEncoder.encode(name, "UTF-8").replace("+", "%20")
                        val connection = URL(url).openConnection() as HttpURLConnection
                        try {
                            connection.connectTimeout = 1800; connection.readTimeout = 2600; connection.instanceFollowRedirects = true
                            connection.setRequestProperty("User-Agent", "PSP-Cheat-DB-Manager-Android/0.7.1")
                            val bytes = if (connection.responseCode == HttpURLConnection.HTTP_OK) connection.inputStream.use { readLimited(it, 4 * 1024 * 1024) } else null
                            name to bytes
                        } finally { connection.disconnect() }
                    })) }
                    val searchDeadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(4)
                    var remaining = probes.size
                    while (remaining > 0 && imageBytes == null) {
                        val timeLeft = searchDeadline - System.nanoTime()
                        if (timeLeft <= 0) break
                        val finished = completion.poll(timeLeft, TimeUnit.NANOSECONDS) ?: break
                        remaining--
                        try { imageBytes = finished.get().second } catch (_: Exception) { }
                    }
                    probes.forEach { if (!it.isDone) it.cancel(true) }
                }
                if (imageBytes == null) {
                    runOnUiThread {
                        if (target == null && currentScreen == "mods" && currentGameId == id && ::coverOverlayView.isInitialized) coverOverlayView.text = "${gameTitle.take(28)} · $id\nSearching cover archive…"
                        if (target === mainCoverImageView && ::selectedGameFile.isInitialized && currentScreen == "search") selectedGameFile.text = "$gameTitle\n$id\nSEARCHING COVER ARCHIVE…"
                    }
                }
                if (imageBytes == null && getSharedPreferences("prefs", 0).getBoolean("steamgrid_cover_enabled", false)) {
                    val apiKey = getSteamGridApiKey()
                    if (!apiKey.isNullOrBlank()) {
                        runOnUiThread {
                            if (target == null && currentScreen == "mods" && currentGameId == id && ::coverOverlayView.isInitialized) coverOverlayView.text = "${gameTitle.take(28)} · $id\nTRYING STEAMGRIDDB…"
                            if (target === mainCoverImageView && ::selectedGameFile.isInitialized && currentScreen == "search") selectedGameFile.text = "$gameTitle\n$id\nTRYING STEAMGRIDDB…"
                        }
                        imageBytes = fetchSteamGridBoxArt(technicalTitle, id, apiKey)
                    }
                }
                val bytes = imageBytes
                if (bytes == null) {
                    runOnUiThread {
                        if (target === mainCoverImageView && ::selectedGameFile.isInitialized && currentScreen == "search") selectedGameFile.text = "$gameTitle\n$id\nNO COVER FOUND · TAP TO RETRY"
                        if (target == null && currentScreen == "mods" && currentGameId == id && ::coverOverlayView.isInitialized) coverOverlayView.text = "${gameTitle.take(28)} · $id\nNO MATCH · TAP TO RETRY"
                        recentCoverStatusViews[id]?.text = "No cover found"
                        if (::status.isInitialized && currentGameId == id) status.text = "No cover match · $id · Change region/title or check Settings → Cover Art"
                    }
                    return@execute
                }
                cacheFile.writeBytes(bytes)
                val bitmap: Bitmap? = BitmapFactory.decodeByteArray(bytes, 0, bytes.size)
                if (bitmap != null) runOnUiThread {
                    // A screen rebuild replaces the ImageView while a lookup may still be running.
                    // Update the currently visible Home view as well as the original request target.
                    if (::mainCoverImageView.isInitialized && currentScreen == "search" && ::gameId.isInitialized && gameId.text.toString().contains(id)) mainCoverImageView.setImageBitmap(bitmap)
                    if (target != null && currentScreen == "search" && ::gameId.isInitialized && gameId.text.toString().contains(id)) target.setImageBitmap(bitmap)
                    if (currentScreen == "games") recentCoverViews[id]?.setImageBitmap(bitmap)
                    else if (currentScreen == "mods" && currentGameId == id && ::coverImageView.isInitialized) coverImageView.setImageBitmap(bitmap)
                    if (currentScreen == "mods" && currentGameId == id && ::coverOverlayView.isInitialized) coverOverlayView.text = "${gameTitle.take(28)} · $id\nBOX ART LOADED · TAP TO REFRESH"
                    recentCoverStatusViews[id]?.text = "Cover art loaded"
                    if (::status.isInitialized && currentGameId == id) status.text = "Cover art loaded · $id"
                }
            } catch (error: Exception) {
                val failureText = if (error is SecurityException) "STEAMGRIDDB KEY REJECTED · CHECK SETTINGS" else "NO COVER FOUND · TAP TO RETRY"
                runOnUiThread {
                    if (target === mainCoverImageView && ::selectedGameFile.isInitialized && currentScreen == "search") selectedGameFile.text = "$gameTitle\n$id\n$failureText"
                    if (target == null && currentScreen == "mods" && currentGameId == id && ::coverOverlayView.isInitialized) coverOverlayView.text = "${gameTitle.take(28)} · $id\n$failureText"
                    recentCoverStatusViews[id]?.text = if (error is SecurityException) "SteamGridDB key rejected · check Settings" else "No cover found"
                    if (::status.isInitialized && currentGameId == id) status.text = if (error is SecurityException) "SteamGridDB key rejected · Check Settings → Cover Art" else "No cover match · $id · Try another region or title"
                }
            } finally { activeCoverSearches.remove(id) }
        }
    }

    private inner class TitleAdapter(private val all: List<GameTitle>) : ArrayAdapter<GameTitle>(this@MainActivity, android.R.layout.simple_dropdown_item_1line, ArrayList(all)) {
        override fun getView(position: Int, convertView: View?, parent: ViewGroup): View {
            val row = (convertView as? TextView) ?: TextView(this@MainActivity).apply { setPadding(18, 14, 18, 14); textSize = 15f }
            row.text = getItem(position)?.toString().orEmpty(); row.setTextColor(colors[2]); row.setBackgroundColor(colors[1]); return row
        }
        override fun getDropDownView(position: Int, convertView: View?, parent: ViewGroup): View {
            val item = getItem(position) ?: return TextView(this@MainActivity)
            val row = (convertView as? LinearLayout) ?: LinearLayout(this@MainActivity).apply { orientation = LinearLayout.VERTICAL; setPadding(16, 10, 16, 10) }
            row.removeAllViews(); row.setBackgroundColor(colors[1])
            row.addView(TextView(this@MainActivity).apply { text = item.title; textSize = 16f; setTextColor(colors[2]) })
            row.addView(TextView(this@MainActivity).apply { text = "Country / region: ${item.region}     Game ID: ${item.id}"; textSize = 12f; setTextColor(colors[4]) })
            return row
        }
        override fun getFilter(): android.widget.Filter = object : android.widget.Filter() {
            override fun performFiltering(constraint: CharSequence?): FilterResults {
                val needle = constraint?.toString()?.trim()?.lowercase(Locale.ROOT).orEmpty()
                val matches = if (needle.isEmpty()) emptyList() else all.asSequence().filter { it.title.lowercase(Locale.ROOT).contains(needle) || it.region.lowercase(Locale.ROOT).contains(needle) || it.id.lowercase(Locale.ROOT).contains(needle) }.toList()
                return FilterResults().apply { values = matches; count = matches.size }
            }
            override fun publishResults(constraint: CharSequence?, results: FilterResults?) {
                clear(); @Suppress("UNCHECKED_CAST") val matches = results?.values as? List<GameTitle> ?: emptyList(); addAll(matches)
                if (matches.isEmpty()) notifyDataSetInvalidated() else notifyDataSetChanged()
            }
        }
    }

    private fun showSources() {
        val labels = arrayOf("CWCheat Database Plus — Saramagrean", "PPSSPP workarounds — LunaMoo")
        val urls = arrayOf("https://github.com/Saramagrean/CWCheat-Database-Plus-/archive/refs/heads/master.zip", "https://github.com/LunaMoo/PPSSPP_workarounds/archive/refs/heads/master.zip")
        AlertDialog.Builder(this).setTitle("Choose a source").setItems(labels) { _, which -> AlertDialog.Builder(this).setTitle("Download source?").setMessage("Download and merge files from ${labels[which]}? This uses mobile data if Wi-Fi is unavailable.").setNegativeButton("Cancel", null).setPositiveButton("Download") { _, _ -> downloadSource(urls[which], labels[which]) }.showThemed() }.setNeutralButton("Import local file") { _, _ -> openDocument(REQ_IMPORT) }.showThemed()
    }
    private fun downloadSource(url: String, source: String) {
        if (::status.isInitialized) status.text = "Downloading $source…"
        showTaskProgress("Downloading source", "Connecting to $source…")
        worker.execute {
            try {
                val c = URL(url).openConnection() as HttpURLConnection
                c.connectTimeout = 20000; c.readTimeout = 45000; c.instanceFollowRedirects = true
                c.setRequestProperty("User-Agent", "PSP-Cheat-DB-Manager-Android/0.7.11")
                val bytes = try {
                    val response = c.responseCode
                    if (response !in 200..299 || c.url.protocol != "https") error("Secure source download failed (HTTP $response).")
                    val expected = c.contentLengthLong
                    c.inputStream.use { readDownloadWithProgress(it, MAX_ARCHIVE_BYTES, expected, source) }
                } finally { c.disconnect() }
                runOnUiThread { setTaskProgress("Checking and merging source data…", null) }
                val parsed = parseImportBytes(bytes, source)
                runOnUiThread { dismissTaskProgress(); completeImport(parsed, "Imported source: $source"); showCornerNotification("Source updated · $source") }
            } catch (e: Exception) {
                runOnUiThread {
                    dismissTaskProgress()
                    if (::status.isInitialized) status.text = "Source failed: ${e.message ?: e.javaClass.simpleName}"
                    showCornerNotification("Source download failed", isError = true)
                }
            }
        }
    }

    private fun showTaskProgress(title: String, detail: String) {
        dismissTaskProgress()
        val panel = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(dp(20), dp(12), dp(20), dp(8)); setBackgroundColor(colors[1]) }
        progressText = TextView(this).apply { text = detail; setTextColor(colors[2]); textSize = 14f; setPadding(0, 0, 0, dp(8)) }
        progressBar = ProgressBar(this, null, android.R.attr.progressBarStyleHorizontal).apply { max = 100; progress = 0; progressTintList = android.content.res.ColorStateList.valueOf(colors[4]); progressBackgroundTintList = android.content.res.ColorStateList.valueOf(colors[3]) }
        panel.addView(progressText)
        panel.addView(progressBar, LinearLayout.LayoutParams(-1, dp(14)))
        val dialog = AlertDialog.Builder(this).setTitle(title).setView(panel).create()
        dialog.setCancelable(false)
        progressDialog = dialog
        dialog.setOnShowListener { styleDialog(dialog); dialog.window?.setLayout((resources.displayMetrics.widthPixels * 0.82f).toInt().coerceAtMost(dp(520)), -2) }
        dialog.show()
    }

    private fun setTaskProgress(detail: String, percent: Int?) {
        runOnUiThread {
            progressText?.text = if (percent == null) detail else "$detail · ${percent.coerceIn(0, 100)}%"
            progressBar?.let { bar -> if (percent == null) { bar.isIndeterminate = true } else { bar.isIndeterminate = false; bar.progress = percent.coerceIn(0, 100) } }
        }
    }

    private fun dismissTaskProgress() {
        progressDialog?.dismiss(); progressDialog = null; progressBar = null; progressText = null
    }

    private fun readDownloadWithProgress(input: java.io.InputStream, limit: Int, expectedBytes: Long, source: String): ByteArray {
        val output = java.io.ByteArrayOutputStream(); val buffer = ByteArray(32 * 1024); var total = 0L
        while (true) {
            val count = input.read(buffer); if (count < 0) break
            total += count
            if (total > limit) error("Download exceeds the ${limit / (1024 * 1024)} MiB source limit")
            output.write(buffer, 0, count)
            val percent = if (expectedBytes > 0L) ((total * 100L) / expectedBytes).toInt().coerceIn(0, 100) else null
            setTaskProgress("Downloading $source · ${total / 1024} KB", percent)
        }
        if (expectedBytes > 0L && total != expectedBytes) error("Download ended early ($total of $expectedBytes bytes); existing data was not changed")
        setTaskProgress("Download complete · 100% · validating archive…", 100)
        return output.toByteArray()
    }

    private fun showCornerNotification(message: String, isError: Boolean = false) {
        if (Looper.myLooper() != Looper.getMainLooper()) { notificationHandler.post { showCornerNotification(message, isError) }; return }
        notificationPopup?.dismiss()
        val activeColors = colors ?: palette(theme)
        val accent = if (isError) Color.rgb(235, 80, 80) else activeColors[4]
        val card = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL; setPadding(dp(12), dp(10), dp(16), dp(10)); background = GradientDrawable().apply { setColor(activeColors[1]); cornerRadius = dp(9).toFloat(); setStroke(dp(2), accent) }; elevation = dp(8).toFloat() }
        card.addView(TextView(this).apply { text = if (isError) "!" else "✓"; textSize = 20f; typeface = Typeface.DEFAULT_BOLD; setTextColor(accent); gravity = Gravity.CENTER; setPadding(0, 0, dp(10), 0) })
        card.addView(TextView(this).apply { text = message; textSize = 13f; setTextColor(activeColors[2]); maxLines = 3; ellipsize = TextUtils.TruncateAt.END })
        val popup = PopupWindow(card, dp(310).coerceAtMost(resources.displayMetrics.widthPixels - dp(24)), ViewGroup.LayoutParams.WRAP_CONTENT, false).apply { isOutsideTouchable = false; isFocusable = false; elevation = dp(8).toFloat(); animationStyle = android.R.style.Animation_Toast }
        notificationPopup = popup
        popup.showAtLocation(window.decorView, Gravity.TOP or Gravity.END, dp(12), dp(14))
        card.alpha = 0f
        card.animate().alpha(1f).setDuration(160).start()
        notificationHandler.postDelayed({ if (notificationPopup === popup) { card.animate().alpha(0f).setDuration(260).withEndAction { popup.dismiss(); if (notificationPopup === popup) notificationPopup = null }.start() } }, 3200)
    }

    private fun styleDialog(dialog: AlertDialog) {
        val activeColors = colors ?: palette(theme)
        dialog.window?.setBackgroundDrawable(GradientDrawable().apply { setColor(activeColors[1]); cornerRadius = dp(10).toFloat(); setStroke(dp(1), activeColors[4]) })
        dialog.findViewById<TextView>(androidxIdAlertTitle())?.apply { setTextColor(activeColors[2]); typeface = Typeface.create("sans-serif-condensed", Typeface.BOLD) }
        dialog.findViewById<TextView>(android.R.id.message)?.setTextColor(activeColors[2])
        for (buttonId in intArrayOf(AlertDialog.BUTTON_POSITIVE, AlertDialog.BUTTON_NEGATIVE, AlertDialog.BUTTON_NEUTRAL)) {
            dialog.getButton(buttonId)?.apply { setTextColor(activeColors[4]); typeface = Typeface.create("sans-serif-condensed", Typeface.BOLD) }
        }
        dialog.listView?.let { list ->
            list.setBackgroundColor(activeColors[1])
            list.divider = android.graphics.drawable.ColorDrawable(activeColors[4]); list.dividerHeight = dp(1)
            list.selector = surface(activeColors[3], activeColors[4])
            for (i in 0 until list.childCount) (list.getChildAt(i) as? TextView)?.setTextColor(activeColors[2])
        }
    }
    private fun androidxIdAlertTitle(): Int = resources.getIdentifier("alertTitle", "id", "android")
    private fun AlertDialog.Builder.showThemed(): AlertDialog {
        val dialog = create()
        dialog.setOnShowListener { styleDialog(dialog) }
        dialog.show()
        return dialog
    }

    private fun openDocument(request: Int) {
        val i = Intent(Intent.ACTION_OPEN_DOCUMENT).apply {
            addCategory(Intent.CATEGORY_OPENABLE)
            type = if (request == REQ_GAME) "*/*" else "*/*"
            putExtra(Intent.EXTRA_MIME_TYPES, if (request == REQ_GAME)
                arrayOf("application/octet-stream", "application/x-iso9660-image", "application/x-chd", "application/chd", "image/chd", "*/*")
            else arrayOf("text/plain", "application/octet-stream", "application/zip", "application/x-zip-compressed", "*/*"))
            putExtra(Intent.EXTRA_TITLE, if (request == REQ_GAME) "Choose PSP ISO, PBP, or CHD" else "Choose cheat database")
        }
        if (request == REQ_GAME) getSharedPreferences("prefs", 0).getString(GAME_TREE_PREF, null)?.let { saved ->
            if (android.os.Build.VERSION.SDK_INT >= 26) i.putExtra(DocumentsContract.EXTRA_INITIAL_URI, Uri.parse(saved))
        }
        try { startActivityForResult(i, request) }
        catch (e: Exception) { status.text = "Could not open Android's file picker: ${e.message ?: "No file picker is available"}" }
    }
    @Deprecated("Use Activity Result APIs for new apps")
    override fun onActivityResult(requestCode: Int, resultCode: Int, data: Intent?) {
        super.onActivityResult(requestCode, resultCode, data)
        if (requestCode == REQ_EXPORT_FOLDER) {
            if (resultCode != RESULT_OK || data?.data == null) { pendingExport = null; status.text = "Export folder selection cancelled."; return }
            val uri = data.data!!
            try {
                val flags = data.flags and (Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_WRITE_URI_PERMISSION)
                contentResolver.takePersistableUriPermission(uri, flags)
                getSharedPreferences("prefs", 0).edit().putString(EXPORT_TREE_PREF, uri.toString()).apply()
                exportFolderLabel.text = exportFolderText()
                status.text = "Export folder saved for next time."
                if (currentScreen == "settings") showSettingsScreen()
                pendingExport?.let { (name, contents) -> pendingExport = null; saveExportToRememberedFolder(name, contents) }
                stopPpssppIniMonitoring()
                startPpssppIniMonitoring()
            } catch (e: Exception) { pendingExport = null; status.text = "Could not remember that folder: ${e.message ?: e.javaClass.simpleName}" }
            return
        }
        if (requestCode == REQ_GAME_FOLDER) {
            if (resultCode == RESULT_OK) data?.data?.let(::saveGameFolder) else pendingFolderScanAfterPick = false
            return
        }
        if (resultCode != RESULT_OK) return
        val uri = data?.data ?: return
        when (requestCode) { REQ_IMPORT -> importUri(uri); REQ_GAME -> inspectGameUri(uri); REQ_EXPORT, REQ_EXPORT_ALL -> writeUri(uri, requestCode) }
    }
    private fun importUri(uri: Uri) {
        status.text = "Reading and checking database…"
        worker.execute {
            try {
                val bytes = contentResolver.openInputStream(uri)!!.use { readLimited(it, MAX_ARCHIVE_BYTES) }
                val source = uri.lastPathSegment ?: "Imported file"
                val parsed = parseImportBytes(bytes, source)
                runOnUiThread { completeImport(parsed, "Imported and merged cheat data") }
            } catch (e: Exception) {
                runOnUiThread { status.text = "Import failed: ${e.message ?: e.javaClass.simpleName}" }
            }
        }
    }
    private fun completeImport(parsed: Map<String, Game>, message: String) {
        try {
            mergeParsed(db, parsed); saveDb(); updateCount(); renderResults()
            val importedCount = parsed.values.sumOf { it.cheats.size }
            status.text = "$message ($importedCount new or matched game records)"
            showCornerNotification("Import complete · $importedCount cheat entries")
        } catch (e: Exception) { status.text = "Could not save imported data: ${e.message ?: e.javaClass.simpleName}" }
    }
    private fun readLimited(input: java.io.InputStream, limit: Int): ByteArray {
        val out = java.io.ByteArrayOutputStream(); val buffer = ByteArray(32 * 1024); var total = 0
        while (true) { val n = input.read(buffer); if (n < 0) break; total += n; if (total > limit) error("File is larger than the ${limit / (1024 * 1024)} MiB mobile import limit"); out.write(buffer, 0, n) }
        return out.toByteArray()
    }
    private fun parseImportBytes(bytes: ByteArray, source: String): Map<String, Game> {
        val parsed = linkedMapOf<String, Game>()
        if (bytes.size >= 4 && bytes[0] == 0x50.toByte() && bytes[1] == 0x4b.toByte()) {
            val z = ZipInputStream(bytes.inputStream()); var e = z.nextEntry; var total = 0L
            while (e != null) {
                val name = e.name.replace('\\', '/'); val base = name.substringAfterLast('/').lowercase(Locale.ROOT)
                val aspectFile = source.contains("aspect", true) && base.endsWith(".ini") && name.split('/').any { it.equals("ppsspp", true) }
                val dbFile = base in listOf("cheat.db", "cheats.db", "cheat.ini", "cheats.ini")
                if (aspectFile || dbFile) {
                    val raw = readLimited(z, MAX_ENTRY_BYTES); total += raw.size; if (total > MAX_EXPANDED_BYTES) error("Archive contents exceed the mobile import limit")
                    var text = raw.toString(Charsets.UTF_8).removePrefix("\uFEFF")
                    if (aspectFile && !Regex("(?m)^\\s*_S\\s+").containsMatchIn(text)) {
                        val m = Regex("([A-Z]{4})[-_ ]?(\\d{5})").find(base.uppercase())
                        if (m != null) { val id = m.groupValues[1] + m.groupValues[2]; text = "_S ${id.take(4)}-${id.drop(4)}\n_G $id\n$text" }
                    }
                    mergeParsed(parsed, parseCheats(text, source))
                    if (dbFile && !source.contains("aspect", true)) break
                }
                e = z.nextEntry
            }
        } else mergeParsed(parsed, parseCheats(bytes.toString(Charsets.UTF_8).removePrefix("\uFEFF"), source))
        if (parsed.values.none { it.cheats.isNotEmpty() }) error("No CWCheat entries found. Check that the ZIP contains cheat.db or PPSSPP game INI files.")
        return parsed
    }
    private fun mergeParsed(target: MutableMap<String, Game>, incomingGames: Map<String, Game>) {
        incomingGames.forEach { (id, incoming) ->
            val game = target.getOrPut(id) { Game(id, incoming.title) }
            if (game.title.isBlank()) game.title = incoming.title
            val known = game.cheats.asSequence().map(::key).toHashSet()
            incoming.cheats.forEach { cheat -> if (known.add(key(cheat))) game.cheats.add(cheat) }
        }
    }
    private fun parseCheats(text: String, source: String): Map<String, Game> { val out = linkedMapOf<String, Game>(); var game: Game? = null; var cheatName: String? = null; var codes = mutableListOf<Pair<String, String>>(); fun finish() { val g = game; val n = cheatName; if (g != null && n != null && codes.isNotEmpty()) g.cheats.add(Cheat(n, codes.toList(), source)); cheatName = null; codes = mutableListOf() }; for (line0 in text.lineSequence()) { val line = line0.trim(); val sm = Regex("^_S\\s+([A-Za-z]{4})[-_ ]?(\\d{5})$").find(line); if (sm != null) { finish(); val id = (sm.groupValues[1] + sm.groupValues[2]).uppercase(); game = out.getOrPut(id) { Game(id, "") }; continue }; val g = game ?: continue; when { line.startsWith("_G ") -> if (g.title.isBlank()) g.title = line.drop(3).trim(); line.startsWith("_C0 ") || line.startsWith("_C1 ") -> { finish(); cheatName = line.drop(4).trim() }; line.startsWith("_L ") && cheatName != null -> { val p = line.drop(3).trim().split(Regex("\\s+")); if (p.size >= 2 && p.take(2).all { it.matches(Regex("(?:0x)?[0-9A-Fa-f]{1,8}")) }) codes.add(p[0] to p[1]) } } }; finish(); return out }
    private fun key(c: Cheat) = c.name.lowercase().replace(Regex("[^a-z0-9]"), "") + "|" + c.codes.joinToString(";") { it.first.uppercase() + ":" + it.second.uppercase() }

    private fun inspectGameUri(uri: Uri) {
        val name = (uri.lastPathSegment ?: "").substringAfterLast('/')
        val id = Regex("[A-Z]{4}[-_ ]?\\d{5}").find(name.uppercase())?.value?.replace(Regex("[-_ ]"), "") ?: ""
        selectedGameFile.text = "Selected game: ${name.ifBlank { "PSP image" }}"
        if (id.isNotBlank()) {
            rememberRecentGame(id); gameId.setText(id); openModsScreen(id)
        } else {
            val stem = name.substringBeforeLast('.', name).lowercase(Locale.ROOT).replace(Regex("[^a-z0-9]"), "")
            val match = titleCatalog.firstOrNull { candidate ->
                val gameName = candidate.title.lowercase(Locale.ROOT).replace(Regex("[^a-z0-9]"), "")
                gameName.length >= 8 && stem.startsWith(gameName)
            }
            if (match != null) {
                rememberRecentGame(match.id); gameId.setText(match.id); title.setText(match.title, false); openModsScreen(match.id)
            } else {
                title.setText(name.substringBeforeLast('.', name)); status.text = "Game selected. Choose its country/title from the suggestions or enter its ID."; title.showDropDown()
            }
        }
    }

    private fun searchCurrentGame() {
        val id = gameId.text.toString().uppercase().replace(Regex("[-_ ]"), "").trim()
        if (!id.matches(Regex("[A-Z]{4}\\d{5}"))) { status.text = "Choose a game title or enter a valid PSP ID (four letters and five digits)."; return }
        openModsScreen(id)
    }

    private fun openModsScreen(id: String) {
        autoSearch?.let { autoSearchHandler.removeCallbacks(it) }; autoSearch = null
        val compact = compactLandscape()
        if (currentGameId != id) selected.clear()
        rememberRecentGame(id)
        currentScreen = "mods"; currentGameId = id
        val game = db[id]
        val catalog = titleCatalog.firstOrNull { it.id == id }
        val displayTitle = game?.title?.takeIf { it.isNotBlank() } ?: catalog?.title ?: id
        val region = catalog?.region ?: "Region not listed"
        root = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(8, 7, 8, 6); setBackgroundColor(colors[0]) }

        // The new console-like dashboard follows the supplied PSP reference: branded
        // top rail, game information at left, a dense mod table, right navigation,
        // and a fixed export/action shelf.
        val top = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL; setPadding(10, 5, 10, 5); background = surface(colors[3], colors[4]) }
        top.addView(TextView(this).apply { text = "PSP CHEAT DB MANAGER"; textSize = if (compact) 18f else 23f; setTextColor(colors[2]); typeface = Typeface.create("sans-serif-condensed", Typeface.BOLD); gravity = Gravity.CENTER_VERTICAL; setPadding(10, 0, 14, 0) }, LinearLayout.LayoutParams(0, -1, 1.6f))
        count = TextView(this).apply { setTextColor(colors[2]); textSize = 14f; gravity = Gravity.RIGHT or Gravity.CENTER_VERTICAL; typeface = Typeface.create("sans-serif-condensed", Typeface.NORMAL); setPadding(8, 0, 8, 0) }
        top.addView(count, LinearLayout.LayoutParams(0, -1, 1.1f))
        top.addView(TextView(this).apply { text = "v0.7.11"; setTextColor(colors[2]); textSize = 13f; gravity = Gravity.CENTER; setPadding(7, 0, 7, 0) })
        root.addView(top, LinearLayout.LayoutParams(-1, if (compact) 50 else 66))

        val workArea = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; setPadding(0, 5, 0, 5) }
        val left = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(10, 10, 10, 8); background = surface(colors[1], colors[4]) }
        val artFrame = FrameLayout(this).apply { background = surface(colors[4], colors[4]); clipToOutline = true }
        coverImageView = ImageView(this).apply { scaleType = ImageView.ScaleType.CENTER_CROP; background = GradientDrawable(GradientDrawable.Orientation.TL_BR, intArrayOf(colors[3], colors[1], colors[3])) }
        artFrame.addView(coverImageView, FrameLayout.LayoutParams(-1, -1))
        coverOverlayView = TextView(this).apply { text = "${displayTitle.take(28)} · $id\nTAP TO SEARCH BOX ART"; textSize = if (compact) 11f else 13f; setTextColor(Color.WHITE); typeface = Typeface.create("sans-serif-condensed", Typeface.BOLD); gravity = Gravity.BOTTOM or Gravity.START; maxLines = 2; ellipsize = TextUtils.TruncateAt.END; setPadding(8, 8, 8, 8); setShadowLayer(4f, 1f, 1f, Color.BLACK); background = GradientDrawable(GradientDrawable.Orientation.BOTTOM_TOP, intArrayOf(0xCC000000.toInt(), Color.TRANSPARENT)) }
        artFrame.addView(coverOverlayView, FrameLayout.LayoutParams(-1, dp(if (compact) 64 else 72), Gravity.BOTTOM))
        artFrame.setOnClickListener {
            status.text = "Searching Libretro PSP box art for $displayTitle…"
            loadCoverArt(id, displayTitle, region, forceSearch = true)
        }
        left.addView(artFrame, LinearLayout.LayoutParams(-1, 0, 1f))
        loadCoverArt(id, displayTitle, region)
        left.addView(TextView(this).apply { text = displayTitle; textSize = if (compact) 15f else 19f; setTextColor(colors[2]); typeface = Typeface.create("sans-serif-condensed", Typeface.BOLD); setPadding(3, 5, 3, 1) })
        left.addView(TextView(this).apply { text = "$id   |   ${countryName(region)}\nPSP GAME"; textSize = if (compact) 11f else 13f; setTextColor(colors[4]); typeface = Typeface.create("sans-serif-condensed", Typeface.NORMAL); setPadding(3, 1, 3, 3) })
        left.addView(TextView(this).apply {
            text = installedIniLine(id) ?: if (installedIniScanComplete) "No installed PPSSPP INI mods found" else "PPSSPP INI status not scanned"
            textSize = if (compact) 10f else 12f; setTextColor(colors[4]); maxLines = 2; ellipsize = TextUtils.TruncateAt.END; setPadding(3, 2, 3, 4)
        })
        left.addView(button(if (isFavorite(id)) "★  FAVORITED" else "☆  ADD FAVORITE") { toggleFavorite(id) }, LinearLayout.LayoutParams(-1, if (compact) 42 else 40))
        left.addView(button("▱  ADD PSP GAME") { showGameImportOptions() }, LinearLayout.LayoutParams(-1, if (compact) 42 else 48))
        left.addView(button("⌕  SEARCH BY TITLE") { returnToSearch(); title.requestFocus() }, LinearLayout.LayoutParams(-1, if (compact) 36 else 48))
        selectedCountLabel = TextView(this).apply { text = "${selected.count { it.first == id }} SELECTED"; setTextColor(colors[4]); textSize = 14f; typeface = Typeface.create("sans-serif-condensed", Typeface.BOLD); setPadding(4, 8, 4, 0) }
        left.addView(selectedCountLabel)
        workArea.addView(left, LinearLayout.LayoutParams(0, -1, .27f))

        val center = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(7, 3, 7, 3) }
        val searchRow = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL }
        query = edit("⌕   Search mods by name").apply { textSize = if (compact) 12f else 14f; setPadding(12, 2, 12, 2) }
        searchRow.addView(query, LinearLayout.LayoutParams(0, if (compact) 36 else 42, 1f))
        searchRow.addView(button("SORT ▾") { showCheatSortPicker() }, LinearLayout.LayoutParams(dp(78), if (compact) 36 else 42))
        center.addView(searchRow)
        val filters = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; setPadding(0, 5, 0, 5) }
        (if (compact) listOf("ALL", "60 FPS") else listOf("ALL", "60 FPS", "3:2", "ULTRAWIDE", "GAMEPLAY", "GRAPHICS")).forEach { f ->
            filters.addView(button(f) { filter = when (f) { "ALL" -> "All"; "60 FPS" -> "60 FPS"; "4:3" -> "4:3"; "3:2" -> "3:2"; "ULTRAWIDE" -> "Ultrawide"; "GAMEPLAY" -> "Gameplay"; else -> "Graphics" }; renderResults() }, LinearLayout.LayoutParams(0, if (compact) 38 else 42, 1f))
        }
        filters.addView(button("FILTER ▾") { showFilterPicker() }, LinearLayout.LayoutParams(0, if (compact) 38 else 42, 1f))
        center.addView(filters)
        val selectionActions = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; setPadding(0, 0, 0, dp(4)) }
        selectVisibleButton = button("SELECT ALL VISIBLE") { toggleVisibleCheatSelection() }
        selectionActions.addView(selectVisibleButton, LinearLayout.LayoutParams(0, if (compact) 34 else 38, 1f))
        center.addView(selectionActions)
        val tableHead = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL; setPadding(8, 4, 8, 4); background = surface(colors[1], colors[4]) }
        tableHead.addView(TextView(this).apply { text = "□"; setTextColor(colors[4]); textSize = 18f; gravity = Gravity.CENTER }, LinearLayout.LayoutParams(dp(38), 34))
        tableHead.addView(tableText("CHEAT NAME"), LinearLayout.LayoutParams(0, 34, 3.1f))
        tableHead.addView(tableText("CATEGORY"), LinearLayout.LayoutParams(0, 34, 1.25f))
        tableHead.addView(tableText("STATUS"), LinearLayout.LayoutParams(0, 34, 1.3f))
        tableHead.addView(tableText("LINES"), LinearLayout.LayoutParams(0, 34, .5f))
        tableHead.visibility = if (compact) View.GONE else View.VISIBLE
        center.addView(tableHead)
        val scroll = ScrollView(this).apply { isFillViewport = true; background = surface(colors[3], colors[4]) }
        results = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL }
        scroll.addView(results)
        center.addView(scroll, LinearLayout.LayoutParams(-1, 0, 1f))
        status = label("Choose one or more mods. All entries are unverified.").apply { textSize = 11f; setTextColor(colors[4]) }
        center.addView(status)
        val exportShelf = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; setPadding(0, 4, 0, 0) }
        val shelfHeight = if (compact) 46 else 56
        exportShelf.addView(button(if (compact) "EXPORT INI" else "▤  EXPORT .INI\n     $id.ini") { exportSelected() }, LinearLayout.LayoutParams(0, shelfHeight, 1f))
        exportShelf.addView(button(if (compact) "EXPORT DB" else "▤  EXPORT cheat.db\n     Merge or New") { exportSelectedForPpsspp() }, LinearLayout.LayoutParams(0, shelfHeight, 1f))
        exportShelf.addView(button(if (compact) "EXPORT ALL" else "▣  EXPORT ALL MODS\n     $id.ini") { exportGame() }, LinearLayout.LayoutParams(0, shelfHeight, 1f))
        exportShelf.addView(button("•••") { showExportActions() }, LinearLayout.LayoutParams(dp(54), shelfHeight))
        center.addView(exportShelf)
        center.addView(TextView(this).apply { text = "Export location: ${shortExportFolder()}   ·   Tap to change"; setTextColor(colors[4]); textSize = 11f; setPadding(5, 2, 5, 0); setOnClickListener { chooseExportFolder() } })
        workArea.addView(center, LinearLayout.LayoutParams(0, -1, .73f))

        val rail = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(3, 2, 3, 2); background = surface(colors[1], colors[4]) }
        if (compact) addCompactRailActions(rail)
        else addFullRailActions(rail)
        workArea.addView(rail, LinearLayout.LayoutParams(dp(if (compact) 52 else 76), -1))
        root.addView(workArea, LinearLayout.LayoutParams(-1, 0, 1f))
        root.addView(controllerFooter("mods"), LinearLayout.LayoutParams(-1, -2))
        setContentView(root); updateCount(); renderResults()
        query.addTextChangedListener(object : TextWatcher {
            override fun beforeTextChanged(s: CharSequence?, start: Int, count: Int, after: Int) {}
            override fun onTextChanged(s: CharSequence?, start: Int, before: Int, count: Int) { renderResults() }
            override fun afterTextChanged(s: Editable?) {}
        })
    }

    private fun dp(value: Int): Int = (value * resources.displayMetrics.density + .5f).toInt()
    private fun surface(color: Int, stroke: Int): GradientDrawable = GradientDrawable().apply { setColor(color); cornerRadius = dp(5).toFloat(); setStroke(dp(1), stroke) }
    private fun tableText(value: String) = TextView(this).apply { text = value; textSize = 11f; setTextColor(colors[2]); typeface = Typeface.create("sans-serif-condensed", Typeface.NORMAL); gravity = Gravity.CENTER_VERTICAL }
    private fun showTitlePicker() {
        if (titleCatalog.isEmpty()) { fetchTitleCatalog(true); Toast.makeText(this, "Loading the PSP game list…", Toast.LENGTH_SHORT).show(); return }
        val options = titleCatalog.take(400).map { "${it.title} · ${countryName(it.region)} · ${it.id}" }.toTypedArray()
        AlertDialog.Builder(this).setTitle("Browse PSP games").setItems(options) { _, which ->
            val entry = titleCatalog[which]; suppressAutoSearch = true; gameId.setText(entry.id); title.setText(entry.title, false); suppressAutoSearch = false; openModsScreen(entry.id)
        }.setNegativeButton("Close", null).showThemed()
    }
    private fun showFilterPicker() {
        val options = arrayOf("All", "60 FPS", "4:3", "3:2", "Ultrawide", "Gameplay", "Graphics", "Other")
        AlertDialog.Builder(this).setTitle("Filter cheats").setItems(options) { _, which -> filter = options[which]; renderResults() }.showThemed()
    }
    private fun showExportActions() {
        val options = arrayOf("Choose export location", "Export every mod for this game")
        AlertDialog.Builder(this).setTitle("Export options").setItems(options) { _, which -> if (which == 0) chooseExportFolder() else exportGame() }.showThemed()
    }

    private fun navigateSection(index: Int) {
        when (index) {
            0 -> openGamesScreen()
            1 -> openDocument(REQ_IMPORT)
            2 -> showExportActions()
            3 -> showRecentOrFavoriteList(true)
            4 -> showRecentOrFavoriteList(false)
            else -> showSettingsScreen()
        }
    }

    private fun returnToSearch() {
        val id = currentGameId
        currentScreen = "search"
        buildUi()
        suppressAutoSearch = true
        gameId.setText(id)
        suppressAutoSearch = false
        val meta = titleCatalog.firstOrNull { it.id == id }
        val gameTitle = meta?.title ?: db[id]?.title?.takeIf { it.isNotBlank() } ?: readLibraryTitle(id)
        meta?.let { title.setText(it.title, false) }
        selectedGameFile.text = if (id.isBlank()) "ＰＳＰ\n\nTAP TO SEARCH COVER ART\n\nADD A GAME\nISO / PBP / CHD" else "Last game: ${meta?.let { "${it.title} (${countryName(it.region)} · $id)" } ?: "$gameTitle · $id"}"
        if (id.matches(Regex("[A-Z]{4}\\d{5}"))) loadCoverArt(id, gameTitle, meta?.region.orEmpty(), mainCoverImageView)
    }

    @Deprecated("Use OnBackPressedDispatcher for new apps")
    override fun onBackPressed() {
        if (currentScreen == "settings") {
            when (settingsOriginScreen) { "mods" -> openModsScreen(currentGameId); "games", "recent", "favorites" -> openCollectionScreen(settingsOriginScreen); else -> returnToSearch() }
        } else if (currentScreen in setOf("mods", "games", "recent", "favorites")) returnToSearch() else super.onBackPressed()
    }

    private fun renderResults() {
        if (currentScreen != "mods") return
        val compact = compactLandscape()
        val id = currentGameId
        results.removeAllViews()
        val game = db[id]
        val all = game?.cheats.orEmpty()
        val q = query.text.toString().trim().lowercase(Locale.ROOT)
        val filteredUnsorted = all.withIndex().filter { (_, cheat) ->
            sourceIsEnabled(cheat.source) && (q.isEmpty() || cheat.name.lowercase(Locale.ROOT).contains(q)) && matches(cheat)
        }
        val filtered = when (cheatSortMode) {
            "Name Z–A" -> filteredUnsorted.sortedByDescending { it.value.name.lowercase(Locale.ROOT) }
            "Category" -> filteredUnsorted.sortedWith(compareBy<IndexedValue<Cheat>> { categoryFor(it.value) }.thenBy { it.value.name.lowercase(Locale.ROOT) })
            "Code lines low to high" -> filteredUnsorted.sortedWith(compareBy<IndexedValue<Cheat>> { it.value.codes.size }.thenBy { it.value.name.lowercase(Locale.ROOT) })
            "Code lines high to low" -> filteredUnsorted.sortedWith(compareByDescending<IndexedValue<Cheat>> { it.value.codes.size }.thenBy { it.value.name.lowercase(Locale.ROOT) })
            else -> filteredUnsorted.sortedBy { it.value.name.lowercase(Locale.ROOT) }
        }
        visibleCheatKeys.clear()
        visibleCheatKeys.addAll(filtered.map { id to it.index })
        val visibleSelected = visibleCheatKeys.count { it in selected }
        if (::selectVisibleButton.isInitialized) selectVisibleButton.text = if (visibleCheatKeys.isNotEmpty() && visibleSelected == visibleCheatKeys.size) "CLEAR VISIBLE ($visibleSelected)" else "SELECT ALL VISIBLE (${visibleCheatKeys.size})"
        if (all.isEmpty()) {
            results.addView(label("No mods loaded for $id. Use DATABASE on the right rail to import a cheat file."))
        } else if (filtered.isEmpty()) {
            results.addView(label("No mods match these filters. Choose ALL or change the search text."))
        } else {
            filtered.forEach { (index, cheat) ->
                val key = id to index
                val isChecked = key in selected
                val rowColor = if (isChecked) colors[4] else if (index % 2 == 0) colors[1] else colors[3]
                val textColor = if (isChecked) Color.rgb(18, 20, 21) else colors[2]
                val row = LinearLayout(this).apply { orientation = if (compact) LinearLayout.VERTICAL else LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL; setPadding(if (compact) 8 else 4, if (compact) 4 else 0, 6, if (compact) 4 else 0); setBackground(surface(rowColor, if (isChecked) colors[4] else colors[3])); minimumHeight = dp(if (compact) 60 else 42); isClickable = true }
                val check = CheckBox(this).apply {
                    buttonTintList = android.content.res.ColorStateList.valueOf(if (isChecked) Color.rgb(18,20,21) else colors[4])
                    this.isChecked = isChecked; contentDescription = "Select ${cheat.name}"; setPadding(3, 0, 0, 0)
                    setOnCheckedChangeListener { _, checked ->
                        if (checked) selected.add(key) else selected.remove(key)
                        val n = selected.count { it.first == id }
                        selectedCountLabel.text = "$n SELECTED"
                        status.text = "$n selected  ·  ${cheat.name}  ·  ${cheat.codes.size} code line(s)"
                    }
                }
                val category = categoryFor(cheat)
                if (compact) {
                    val mainLine = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL }
                    mainLine.addView(check, LinearLayout.LayoutParams(dp(40), dp(40)))
                    mainLine.addView(TextView(this).apply { text = cheat.name; textSize = 16f; setTextColor(textColor); typeface = Typeface.create("sans-serif-condensed", Typeface.BOLD); gravity = Gravity.CENTER_VERTICAL; maxLines = 1; ellipsize = android.text.TextUtils.TruncateAt.END }, LinearLayout.LayoutParams(0, dp(36), 1f))
                    mainLine.addView(TextView(this).apply { text = "›"; textSize = 22f; setTextColor(textColor); gravity = Gravity.CENTER }, LinearLayout.LayoutParams(dp(24), dp(36)))
                    row.addView(mainLine, LinearLayout.LayoutParams(-1, dp(36)))
                    row.addView(TextView(this).apply { text = "$category  ·  Unverified  ·  ${cheat.codes.size} line(s)  ·  Tap for code"; textSize = 11f; setTextColor(if (isChecked) textColor else colors[4]); gravity = Gravity.CENTER_VERTICAL; setPadding(dp(42), 0, 2, 0); maxLines = 1; ellipsize = android.text.TextUtils.TruncateAt.END }, LinearLayout.LayoutParams(-1, dp(17)))
                    row.setOnClickListener { showCheatDetails(cheat, key in selected) }
                } else {
                    row.orientation = LinearLayout.HORIZONTAL
                    row.addView(check, LinearLayout.LayoutParams(dp(38), dp(42)))
                    row.addView(TextView(this).apply { text = cheat.name; textSize = 14f; setTextColor(textColor); typeface = Typeface.create("sans-serif-condensed", Typeface.NORMAL); gravity = Gravity.CENTER_VERTICAL; maxLines = 1; ellipsize = android.text.TextUtils.TruncateAt.END }, LinearLayout.LayoutParams(0, dp(42), 3.1f))
                    row.addView(TextView(this).apply { text = category; textSize = 12f; setTextColor(if (!isChecked && category != "Other") colors[4] else textColor); typeface = Typeface.create("sans-serif-condensed", Typeface.NORMAL); gravity = Gravity.CENTER_VERTICAL; maxLines = 1 }, LinearLayout.LayoutParams(0, dp(42), 1.25f))
                    row.addView(TextView(this).apply { text = "Unverified"; textSize = 12f; setTextColor(if (isChecked) textColor else Color.rgb(142,177,190)); typeface = Typeface.create("sans-serif-condensed", Typeface.NORMAL); gravity = Gravity.CENTER_VERTICAL }, LinearLayout.LayoutParams(0, dp(42), 1.3f))
                    row.addView(TextView(this).apply { text = cheat.codes.size.toString(); textSize = 13f; setTextColor(textColor); gravity = Gravity.CENTER }, LinearLayout.LayoutParams(0, dp(42), .5f))
                    row.addView(TextView(this).apply { text = "›"; textSize = 22f; setTextColor(textColor); gravity = Gravity.CENTER }, LinearLayout.LayoutParams(dp(24), dp(42)))
                    row.setOnClickListener { showCheatDetails(cheat, key in selected) }
                }
                results.addView(row)
            }
        }
        val n = selected.count { it.first == id }
        if (all.isNotEmpty() && filtered.isNotEmpty()) status.text = "${filtered.size} MODS SHOWN  ·  $n SELECTED  ·  Unverified codes"
        if (::selectedCountLabel.isInitialized) selectedCountLabel.text = "$n SELECTED"
    }

    private fun toggleVisibleCheatSelection() {
        if (visibleCheatKeys.isEmpty()) return
        val allVisibleSelected = visibleCheatKeys.all { it in selected }
        if (allVisibleSelected) selected.removeAll(visibleCheatKeys.toSet()) else selected.addAll(visibleCheatKeys)
        val countForGame = selected.count { it.first == currentGameId }
        selectedCountLabel.text = "$countForGame SELECTED"
        status.text = if (allVisibleSelected) "Cleared visible mod selections." else "Selected ${visibleCheatKeys.size} visible mod(s)."
        renderResults()
    }

    private fun showCheatDetails(cheat: Cheat, isSelected: Boolean) {
        val codeText = cheat.codes.joinToString("\n") { (left, right) -> "$left $right" }.ifBlank { "No code lines were found in this entry." }
        val details = TextView(this).apply { text = "${categoryFor(cheat)} · Unverified · ${cheat.codes.size} line(s)\n\n$codeText"; textSize = 14f; setTextColor(colors[2]); setPadding(dp(18), dp(12), dp(18), dp(12)) }
        val scroll = ScrollView(this).apply { addView(details) }
        AlertDialog.Builder(this).setTitle(cheat.name).setView(scroll)
            .setPositiveButton(if (isSelected) "Remove selection" else "Select mod") { _, _ ->
                val key = currentGameId to (db[currentGameId]?.cheats?.indexOf(cheat) ?: -1)
                if (key.second >= 0) { if (isSelected) selected.remove(key) else selected.add(key); renderResults() }
            }
            .setNegativeButton("Close", null).showThemed()
    }

    private fun shortExportFolder(): String {
        val saved = getSharedPreferences("prefs", 0).getString(EXPORT_TREE_PREF, null) ?: return "Choose once"
        return Uri.parse(saved).lastPathSegment.orEmpty().substringAfterLast(':').substringAfterLast('/').ifBlank { "Remembered" }
    }
    private fun categoryFor(c: Cheat): String {
        val n = c.name.lowercase()
        return when {
            n.contains("60fps") || n.contains("60 fps") || n.contains("60 hz") -> "60 FPS"
            n.contains("4:3") || n.contains("4x3") || n.contains("3:2") || n.contains("3x2") || n.contains("ultrawide") || n.contains("21:9") || n.contains("aspect") || n.contains("widescreen") -> "Graphics"
            listOf("texture", "resolution", "graphics", "shader", "visual", "screen", "render").any(n::contains) -> "Graphics"
            listOf("health", "ammo", "money", "unlock", "infinite", "damage", "speed", "item", "level").any(n::contains) -> "Gameplay"
            else -> "Other"
        }
    }
    private fun matches(c: Cheat): Boolean = when(filter) {
        "60 FPS" -> categoryFor(c) == "60 FPS"
        "4:3" -> c.name.contains("4:3", true) || c.name.contains("4x3", true) || c.name.contains("4 by 3", true)
        "3:2" -> c.name.contains("3:2", true) || c.name.contains("3x2", true)
        "Ultrawide" -> c.name.contains("ultrawide", true) || c.name.contains("21:9", true) || c.name.contains("wide screen", true)
        "Gameplay" -> categoryFor(c) == "Gameplay"
        "Graphics" -> categoryFor(c) == "Graphics"
        "Other" -> categoryFor(c) == "Other"
        else -> true
    }
    private fun exportSelected() { val id = currentGameId; val entries = selected.mapNotNull { (gid, index) -> db[gid]?.cheats?.getOrNull(index) }; if (entries.isEmpty()) { status.text = "Select at least one cheat first."; return }; launchCreate("$id.ini", REQ_EXPORT) }
    private fun exportGame() { val id = currentGameId; if (db[id]?.cheats.isNullOrEmpty()) { status.text = "No cheats loaded for this game."; return }; launchCreate("${id}.ini", REQ_EXPORT_ALL) }
    private fun exportSelectedForPpsspp() {
        val id = currentGameId
        val chosen = selected.filter { it.first == id }.mapNotNull { (_, index) -> db[id]?.cheats?.getOrNull(index) }
        if (chosen.isEmpty()) { status.text = "Select at least one mod first."; return }
        try {
            // PPSSPP's database importer reads cheat.db and imports matching _S entries
            // only when the user invokes Import from cheat.db on that game's Cheats screen.
            val games = linkedMapOf<String, Game>()
            readExistingCheatDb()?.let { existing -> mergeParsed(games, parseCheats(existing, "Existing cheat.db")) }
            val titleText = titleCatalog.firstOrNull { it.id == id }?.title ?: db[id]?.title ?: id
            val targetGame = games.getOrPut(id) { Game(id, titleText) }
            if (targetGame.title.isBlank() || targetGame.title == id) targetGame.title = titleText
            val known = targetGame.cheats.map(::key).toHashSet()
            chosen.forEach { if (known.add(key(it))) targetGame.cheats.add(it) }
            val contents = serializeDatabase(games)
            saveExportToRememberedFolder("cheat.db", contents)
        } catch (e: Exception) {
            status.text = "Could not prepare PPSSPP cheat.db: ${e.message ?: e.javaClass.simpleName}"
        }
    }
    private fun readExistingCheatDb(): String? {
        val saved = getSharedPreferences("prefs", 0).getString(EXPORT_TREE_PREF, null) ?: return null
        val tree = Uri.parse(saved)
        val rootId = DocumentsContract.getTreeDocumentId(tree)
        val children = DocumentsContract.buildChildDocumentsUriUsingTree(tree, rootId)
        contentResolver.query(children, arrayOf(DocumentsContract.Document.COLUMN_DOCUMENT_ID, DocumentsContract.Document.COLUMN_DISPLAY_NAME), null, null, null)?.use { cursor ->
            val idColumn = cursor.getColumnIndexOrThrow(DocumentsContract.Document.COLUMN_DOCUMENT_ID)
            val nameColumn = cursor.getColumnIndexOrThrow(DocumentsContract.Document.COLUMN_DISPLAY_NAME)
            while (cursor.moveToNext()) if (cursor.getString(nameColumn).equals("cheat.db", true)) {
                val uri = DocumentsContract.buildDocumentUriUsingTree(tree, cursor.getString(idColumn))
                return contentResolver.openInputStream(uri)?.use { readLimited(it, 96 * 1024 * 1024).toString(Charsets.UTF_8).removePrefix("\uFEFF") }
            }
        }
        return null
    }
    private fun launchCreate(name: String, request: Int) {
        val id = currentGameId
        if (!id.matches(Regex("[A-Z]{4}\\d{5}"))) { status.text = "Choose a game with a valid title ID before exporting."; return }
        val fileName = "$id.ini"
        val contents = if (request == REQ_EXPORT) selectedIni() else gameIni()
        saveExportToRememberedFolder(fileName, contents)
    }
    private fun writeUri(uri: Uri, request: Int) { try { val output = if (request == REQ_EXPORT) selectedIni() else gameIni(); contentResolver.openOutputStream(uri, "wt")!!.bufferedWriter().use { it.write(output) }; status.text = "Export saved. Open its folder in the file picker if you want to share or move it." } catch (e: Exception) { status.text = "Export failed: ${e.message}" } }
    private fun header(id: String, name: String) = "_S ${id.take(4)}-${id.drop(4)}\n_G ${name.replace(Regex("[\\r\\n\\u0000]"), " ")}\n"
    private fun entryText(c: Cheat) = buildString { append("_C0 ${c.name.replace(Regex("[\\r\\n\\u0000]"), " ")}\n"); c.codes.forEach { append("_L ${it.first} ${it.second}\n") } }
    private fun selectedIni(): String { val id = currentGameId; val g = db[id]!!; val displayTitle = titleCatalog.firstOrNull { it.id == id }?.title ?: g.title; return header(id, displayTitle) + selected.filter { it.first == id }.mapNotNull { (_, ix) -> db[id]?.cheats?.getOrNull(ix) }.joinToString("") { entryText(it) } }
    private fun gameIni(): String { val id = currentGameId; val g = db[id]!!; val displayTitle = titleCatalog.firstOrNull { it.id == id }?.title ?: g.title; return header(id, displayTitle) + g.cheats.joinToString("") { entryText(it) } }
    private fun serializeDatabase(games: Map<String, Game>): String = games.values.joinToString("\n") { g -> header(g.id, g.title) + g.cheats.joinToString("") { entryText(it) } }
    private fun safeFile(s: String) = s.replace(Regex("[^A-Za-z0-9_.-]"), "_")

    private fun updateCount() { if (::count.isInitialized) count.text = "${db.values.sumOf { it.cheats.size }} cheats" }
    private fun saveDb() { val root = JSONObject(); val games = JSONArray(); db.values.forEach { g -> val obj = JSONObject().put("id", g.id).put("title", g.title); val cs = JSONArray(); g.cheats.forEach { c -> val co = JSONArray(); c.codes.forEach { co.put(JSONArray().put(it.first).put(it.second)) }; cs.put(JSONObject().put("name", c.name).put("source", c.source).put("codes", co)) }; obj.put("cheats", cs); games.put(obj) }; root.put("games", games); openFileOutput("cheats.json", MODE_PRIVATE).use { it.write(root.toString().toByteArray()) } }
    private fun loadDb() { val prefs = getSharedPreferences("prefs", 0); theme = migrateTheme(prefs.getString("theme", "Ghost Protocol") ?: "Ghost Protocol"); prefs.edit().putString("theme", theme).apply(); try { val root = JSONObject(openFileInput("cheats.json").bufferedReader().use { it.readText() }); val games = root.getJSONArray("games"); for (i in 0 until games.length()) { val x = games.getJSONObject(i); val g = Game(x.getString("id"), x.optString("title")); val cs = x.getJSONArray("cheats"); for (j in 0 until cs.length()) { val c = cs.getJSONObject(j); val codes = c.getJSONArray("codes"); val rows = (0 until codes.length()).map { val a = codes.getJSONArray(it); a.getString(0) to a.getString(1) }; g.cheats.add(Cheat(c.getString("name"), rows, c.optString("source", "Imported"))) }; db[g.id] = g } } catch (_: Exception) {} }
    override fun onDestroy() { stopPpssppIniMonitoring(); worker.shutdown(); coverWorker.shutdown(); coverProbeWorkers.shutdownNow(); super.onDestroy() }

    companion object { val SERIAL_PATTERN = Regex("([A-Z]{4})[-_ ]?(\\d{5})"); const val REQ_IMPORT = 1; const val REQ_GAME = 2; const val REQ_EXPORT = 3; const val REQ_EXPORT_ALL = 4; const val REQ_EXPORT_FOLDER = 6; const val REQ_GAME_FOLDER = 7; const val EXPORT_TREE_PREF = "export_tree_uri"; const val GAME_TREE_PREF = "game_tree_uri"; const val MAX_ARCHIVE_BYTES = 32 * 1024 * 1024; const val MAX_ENTRY_BYTES = 16 * 1024 * 1024; const val MAX_EXISTING_INI_FILE_BYTES = 2 * 1024 * 1024; const val MAX_EXISTING_INI_TOTAL_BYTES = 48 * 1024 * 1024; const val MAX_EXISTING_INI_FILES = 3000; const val INI_FOLDER_POLL_MS = 4000L; const val INI_CHANGE_DEBOUNCE_MS = 650L; const val MAX_EXPANDED_BYTES = 96L * 1024 * 1024; const val MAX_CATALOG_BYTES = 24 * 1024 * 1024; const val TITLE_CATALOG_FILE = "psp-title-catalog.csv"; const val TITLE_CATALOG_URL = "https://raw.githubusercontent.com/hrydgard/ppsspp/master/assets/redump.csv" }
}

