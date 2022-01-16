// :: Info
//    NAME      ForkKILLET's Utilities (fkutil)
//    AUTHOR    ForkKILLET

// :: Import

const http		= require("http")
const https		= require("https")
const iconv		= require("iconv-lite")
const BufferH	= require("bufferhelper")
const zlib		= require("zlib")
const {
	inspect, format
}				= require("util")

// :: Main

// :::: Ext     lv.0

Error.em = (title, msg) => Error(`\x1B[31m${title}: ${msg}\x1B[0m`)
Error.unreachable = () => Error.em("???", "It's unreachable! You can never see this f**king error!")

Date.prototype.format = function(f, UTC) {
    UTC = UTC ? "UTC" : ""
    const re = {
        "y+": this[`get${UTC}FullYear`](),
        "m+": this[`get${UTC}Month`]() + 1,
        "d+": this[`get${UTC}Date`](),
        "H+": this[`get${UTC}Hours`](),
        "M+": this[`get${UTC}Minutes`](),
        "S+": this[`get${UTC}Seconds`](),
        "s" : this[`get${UTC}Milliseconds`]()
    }
    for (let r in re) if (RegExp(`(${r})`).test(f))
        f = f.replace(RegExp.$1,
            ("000" + re[r]).substr((re[r].toString()).length + 3  - RegExp.$1.length)
        )
    return f
}
Date.fromTimeZone = n => new Date(Date.now() + n * 60 * 60 * 1000)

String.prototype.reverse = function() {
    return this.split("").reverse().join("")
}
String.prototype.indent = function(n, tab) {
    return this.replace(/^/mg, tab ? "\t".repeat(n) : " ".repeat(n * 4))
}
String.prototype.toInitialCase = function() {
	return this[0].toUpperCase() + this.slice(1)
}
String.prototype.displayLength = function() {
	return [ ...this ].reduce((a, c) => a + (c.charCodeAt() > 127 ? 2 : 1), 0)
}
String.prototype.isEscapedAt = function(i, ch = "\\") {
	let e = 0; while (this[i - e - 1] === ch) e ++
	return e % 2 === 1
}

Number.prototype.toPercent = function() {
    return (this * 100).toFixed(1) + "%"
}

Object.fromSymbolNames = (...arr) => {
    const obj = {}
    arr.flat().forEach(n => obj[n] = Symbol(n))
    return obj
}

Array.fromElementOrArray = i => Is.array(i) ? i : [ i ]
Array.fromLength = (l, v) => Is.undef(v)
	? g => Array.from({ length: l }, g)
	: new Array(l).fill(v)

// :::: Tool    lv.0

const EF = () => {}

const sleep = ms =>
    new Promise(resolve => setTimeout(resolve, ms))

function ski(key, src, dft) { // Note: search key in
    let v = src?.[key] ?? (
        dft._keyQuote ? ski(dft.k, src) : (
        dft._keyCallback ? dft.f?.(key, src) :
        dft
    ))
    if (v?._keyQuote) return ski(v.k, src, dft)
    return v
}

ski.q = k => ({ k, _keyQuote: true })
ski.f = f => ({ f, _keyCallback: true })

function bindo(o, filter) {
	let that = {}
	for (let k in o) {
		if (k.match(filter)) continue
		that[k] = Is.func(o[k]) ? o[k].bind(o) : o[k]
	}
	return that
}

class _c_Is {
    // :::::: basic type

    type        = (x, t) => typeof x === t
    _w_type     = t => x => this.type(x, t)

    types       = (x, ...ts) => ts.flat().includes(typeof x)

    string      = this._w_type("string")
    str         = this.string

    number      = this._w_type("number")
    num         = this.number

    bigint      = this._w_type("bigint")

    func        = this._w_type("function")
    fun         = this.func

    boolean     = this._w_type("boolean")
    bool        = this.boolean

    object      = this._w_type("object")
    obj         = this.object

    symbol      = this._w_type("symbol")
    sym         = this.symbol

    simple      = x => this.string(x) || this.number(x) || this.bigint(x) || this.boolean(x)

    // :::::: judge mode

    judge       = (x, rule, final) => {
        if (! this.func(rule)) {
            rule = ski(rule, {
                any:    (r, p) => ({ pass: p || r, forcepass: r }),
                anyway: (r, p) => ({ pass: p || r, forcepass: r === "forcepass" }),
                all:    (r, p) => ({ pass: (p || p === null) && r, forcepass: r === "forcepass" }),
                none:   (r, p) => ({ pass: (p || p === null) && !r, forcepass: false })
            }, ski.q("all"))
        }
        if (! this.func(final)) {
            final = ski(final, {
                assert: () => {
                    if (! r) throw Error.em("Is.judge",
                        `Assert failed; Rule: ${rule}; More assert info: see Cc.`)
                    return true
                },
                result: p => p
            }, ski.q("result"))
        }

        const IsJ = {
            _forcepass: false, _pass: null,
            q() { return final(this._pass) }
        }
        for (let i in this) {
            if ((i[0] === "_" || i === "judge") && ! i.startsWith("_cor")) continue
            else if (this.func(this[i])) IsJ[i] = (...p) => {
                if (! IsJ._forcepass) ({
                        pass: IsJ._pass,
                        forcepass: IsJ._forcepass
                    } = rule(
                        this[i]((x?._judge && this.func(x)) ? x() : x, ...p), IsJ._pass,
                        { J: IsJ, name: i, param: p, func: this[i] }
                    )
                )
                return IsJ
            }
        }
        return IsJ
    }
    j           = this.judge

    // :::::: generic

    eq          = (x, a) => x === a

    len         = (x, l) => x?.length === l

    checkby     = (x, f) => f(x)

    // :::::: class type

    insts       = (x, i) => x instanceof i
    _w_insts    = i => x => this.insts(x, i)

    regexp      = this._w_insts(RegExp)
    re          = this.regexp

    array       = this._w_insts(Array)
    arr         = this.array

    date        = this._w_insts(Date)

    // :::::: about number

    nan         = x => isNaN(x)
    int         = x => this.number(x) && (x % 1 === 0)

    pos         = x => this.number(x) && x > 0
    pos0        = x => this.number(x) && x >= 0
    neg         = x => this.number(x) && x < 0
    neg0        = x => this.number(x) && x <= 0

    compare     = (x, op, a, b) => ski(op, {
        "lt":   (x, a) => x < a,
        "<":    ski.q("lt"),
        "))":   ski.q("lt"),


        "le":   (x, a) => x <= a,
        "<=":   ski.q("le"),
        ")]":   ski.q("le"),

        "gt":   (x, a) => x > a,
        ">":    ski.q("gt"),
        "((":   ski.q("gt"),

        "ge":   (x, a) => x >= a,
        ">=":   ski.q("ge"),
        "[(":   ski.q("ge"),

        "ltgt": (x, a, b) => a < x && x < b,
        "in":   ski.q("ltgt"),
        "<<":   ski.q("ltgt"),
        "()":   ski.q("ltgt"),

        "legt": (x, a, b) => a <= x && x < b,
        "<=<":  ski.q("legt"),
        "[)":   ski.q("legt"),

        "ltge": (x, a, b) => a < x && x <= b,
        "<<=":  ski.q("ltge"),
        "(]":   ski.q("ltge"),

        "lege": (x, a, b) => a <= x && x <= b,
        "IN":   ski.q("lege"),
        "<=<=": ski.q("lege"),
        "[]":   ski.q("lege"),
    })(x, a, b)
    cmp         = this.compare
    _w_compare  = op => (x, ...p) => this.compare(x, op, ...p)

    lt          = this._w_compare("lt")
    le          = this._w_compare("le")
    gt          = this._w_compare("gt")
    ge          = this._w_compare("ge")
    ltgt        = this._w_compare("ltgt")
    legt        = this._w_compare("legt")
    ltge        = this._w_compare("ltge")
    lege        = this._w_compare("lege")

    // :::::: about string

    numstr      = x => this.number(x) || (this.string(x) && !this.nan(Number(x)))
    char        = x => this.string(x) && this.len(x, 1)

    // :::::: about empty

    nul         = x => x === null
    nil         = this.nul

    undef       = x => x === undefined
    udf         = this.undef

    empty       = x => x == null
    fake        = x => !x

    // :::::: about object

    objectR     = x => this.object(x) && ! this.nul(x)
    objR        = this.objectR

    objectE     = x => this.objectR(x) && Object.getOwnPropertyNames(x).length === 0
    objE        = this.objectE

    // :::::: about array

    among       = (x, ...arr) => arr.flat().includes(x)

    // :::::: forcepass

    _w_able     = f => (...p) => f(p) ? "forcepass" : true

    nullable    = this._w_able(this.empty)
    eqable      = this._w_able(this.eq)
    amongable   = this._w_able(this.among)

    // :::::: correcter

    _corV       = v => ({ _cor: v })

    smartype    = (x, t) => {
        if (this.type(x, t)) return true
        if ((t === "undefined" || t === "null") && x == null) return this._corV(eval(t))
        if (t === "number" && this.numstr(x)) return this._corV(Number(x))
        if (t === "string" && x?.toString) return this._corV(x.toString())
    }
}
const Is = new _c_Is()

ski.type = (key, src, dft) => {
    let type = typeof key
    for (let i of [ "regexp", "array", "date" ])
        if (Is[i](key)) type = i
    return ski(type, src, dft)
}

function Cc(x, n) {
    const cs = [], xd = () => x // Note: Dynamic x.
    xd._judge = true
    const IsJ = Is.judge(xd,
        (r, _, e) => {
            cs.push(e)
            if (r._cor) x = r._cor
            if (r) return { pass: true, forcepass: r === "forcepass" }
            throw Error.em("Cc",
                `Checkee ${n} requires ${e.name}${e.param?.length ? " " + e.param : ""}, but got ${x}.`
            ) // TODO: dull work
        },
        () => x
    )
    Object.defineProperty(IsJ, "r", {
        get() { return IsJ.q() }
    })
    return IsJ
}

function exT(str, tem) {
	let i = str.length - 1
	while (i > 0) {
		i = str.lastIndexOf("{", i) - 1
		const tt = exT.ch2tt[str[i]]
		if (! tt) continue
		if (str.isEscapedAt(i)) continue
		let j = i + 2; while (j > 0) {
			j = str.indexOf("}", j)
			if (str.isEscapedAt(j)) continue
			break
		}
		if (j < 0) throw `unmatched ${ str[i] }{`
		const s = str.slice(i + 2, j).trim()
		let t; switch (tt) {
		case exT.tt.SIMPLE:
			t = tem[s]
			if (Is.empty(t)) throw `undefined \${ ${s} }`
			if (Is.simple(t)) r = t
			else throw `unsimple \${ ${s} }`
			break
		case exT.tt.FUNC:
			const [ n, ...p ] = s.split("|").map(s => s.trim())
			t = tem[n]
			if (Is.empty(t)) throw `undefined !{ ${s} }`
			if (Is.func(t)) r = t(...p)
			else throw `uncallable !{ ${s} }`
			break
		}
		str = str.slice(0, i) + r + str.slice(j + 1)
	}

    return str
}
exT.ch2tt = { "$": 1, "!": 2 }
exT.tt = { SIMPLE: 1, FUNC: 2 }
exT.reflect = (processer, d_tem) => (str, tn, tem) => {
    const t = {}
	tem = { ...d_tem, ...tem }
    if (! tn.startsWith("exT:")) tn = "exT:" + tn
    for (let n in tem) {
        if (Is.simple(tem[n])) {
            t[n] = tem[n]
			continue
        }
        if (Is.func(tem[n])) {
            t[n] = (...p) => tem[n]({
                tem: tn,
                func: tn + "!" + n,
                param: (idx, pn) => tn + "!" + n + ":" + idx + "#" + pn,
            }, ...p)
        }
    }
    processer(exT(str, t))
}

const Logger = o => ({
	opt: o ?? {},
	bind() {
		return bindo(this, /^(_|bind$)/)
	},
	_(s) { // Note: CSI.
		return this.opt.noColor ? "" : "\x1B[" + s
	},
	$(s, m) {
		const csi = this._(s)
		return csi + String(m).replaceAll(this._("0m"), csi) + this._("0m")
	},
    div(t, u, d) {
        this.opt.drop || process.stdout.write(
            "\n".repeat(u ?? 1) +
            "-".repeat(10) +
            "=".repeat(5) +
            (t ? " " +  this._("1;34m") + t + this._("0m") + " " : "") +
            "=".repeat(5) +
            "-".repeat(10) +
            "\n".repeat(d ?? 1)
        )
    },
    log(...p) {
        this.opt.drop || console.log(...p)
    },
	logi(m) {
		this.opt.drop || process.stdout.write(m)
	},
    debug(f, ...p) {
        if (this.opt.dirObj && m.length === 1 && Is.obj(m[0]))
            return console.dir(f, { depth: Infinity })
        if (this.opt.debug) console.log(f, ...p)
    },
    warn(f, ...p) {
		this.opt.drop || console.warn(this.$("33m", f), ...p)
    },
    err(f, ...p) {
		this.opt.drop || console.error(this.$("31m", f), ...p)
    },
    fatal(f, ...p) {
        m = format(this.$("31m", f), ...p)
        if (this.opt.debug) throw m
        else {
			this.opt.drop || console.error(m)
			this.div("EOE", 1, 1)
			process.exit()
		}
    },
	catch(f) {
		try { return f() }
		catch (err) { this.opt.drop || this.warn(err) }
	},
    hili(m, c = 2) {
        return this.$(`3${c}m`, m)
    },
	hiqt(s, ...t) {
		let r = s[0]
		for (let i = 1; i < s.length; i ++) {
			r += `"` + this.hili(t[i - 1]) + `"` + s[i]
		}
		return r
	},
	bold(m) {
		return this.$("1m", m)
	},
	table(t, pad) {
		return t.map(r => r.map((c, i) =>
			c + " ".repeat(pad[i] ? pad[i] - c.replace(/\x1B\[.+?m/g, "").displayLength() : 0)
		).join("")).join("\n")
	},
    code(m) {
        return m
            .replace(/^/mg, this._("48;5;158;32m"))
            .replace(/$/mg, this._("0m"))
    },
    extlog(...p) {
		this.opt.drop || exT.reflect(console.log, this.opt.dftTem)(...p)
	}
})

// :::: Ext     1v.1

Object.clone = src => {
    if (Is.judge(src, "any").simple().empty().re().q()) return src

    const res = Is.arr(src) ? [] : {}
    for (let i in src) res[i] = Object.clone(src[i])
    return res
}

Object.path = (obj, path, create, val) => {
	if (! path.match(/^[.[]/)) path = "." + path

	const rsit = path.matchAll(/\.([_a-zA-Z][0-9_a-zA-Z]*)|\[(\d+)]/g)
	let rs, o = obj, pa_o, k, pa_k, t
	// Note:
	// a.b.c
	// o					pa_o				k		pa_k
	// { a: b: { c: 1 } }	undefined			"a"		undefined
	// { b: { c: 1 } }		{ a: b: { c: 1 } }	"b"		"a"
	// { c: 1}				{ b: { c: 1 } }		"c"		"b"

	while (! (rs = rsit.next()).done) {
		t = !! rs.value[1] // Note: 0 Number, 1 String.
		k = t ? rs.value[1] : Number(rs.value[2])

		if (Is.objR(o)) {
			if (t ^ Is.arr(o)) ;
			else if (create) throw "Path type conflicted."
		}

		else if (Is.udf(o)) {
			if (create) o = pa_o[pa_k] = t ? {} : []
			else throw "Path includes undefined."
		}
		else if (create) throw "Path type conflicted."

		pa_o = o
		o = o[k]
		pa_k = k
	}

	if (create) pa_o[pa_k] = val

	return pa_o[pa_k]
}

// :::: Tool    lv.2

function serialize(src, opt) {
    return JSON.stringify(src, (_, v) => {
        if (opt?.regexp && Is.regexp(v)) return v.source
        return v
    }, opt.indent ?? 4)
}

const httpx = {
	get: (url, opt) => new Promise((resolve, reject) => {
		ski(url.match(/^(https?):\/{2}/)?.[1], { http, https }, ski.f(() => {
			reject(`Unknown protocol.\nURL: ${url}."`)
		})).get(url, opt ?? {}, res => {
			if (res.statusCode !== 200) {
				res.resume()
				reject(res.statusCode)
			}

			const headers = Object.fromEntries(res.rawHeaders.map((v, k, a) =>
				k & 1 ? undefined : [ v, a[k + 1] ]).filter(i => i))
			const charset = headers["Content-Type"].match(/charset=(.+)$/)?.[1] ?? "utf-8"
			const gzipped = headers["Content-Encoding"] === "gzip"

			const bh = new BufferH()

			res.on("data", chunk => bh.concat(chunk))
			res.on("end", async () => {
				let bf = bh.toBuffer()
				if (gzipped) bf = await zlib.gunzip(bf)
				resolve(iconv.decode(bf, charset))
			})
		}).on("error", reject)
	})
}

// :: Export

module.exports = {
    EF,
    Is, Cc, ski,
    sleep, httpx, exT, exTemplate: exT, serialize,
    Logger
}

