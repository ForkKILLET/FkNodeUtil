// :: Info
//    NAME      ForkKILLET's Utilities (fkutil)
//    AUTHOR    ForkKILLET

// :: Import

const http      = require("http")
const https     = require("https")
const iconv     = require("iconv-lite")
const BufferH   = require("bufferhelper")
const zlib		= require("zlib")

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
String.prototype.startWith = function(s) {
    return this.indexOf(s) === 0
}
String.prototype.endWith = function(s) {
    return this.lastIndexOf(s) + s.length === this.length
}
String.prototype.indent = function(n, tab) {
    return this.replace(/^/mg, tab ? "\t".repeat(n) : " ".repeat(n * 4))
}
String.prototype.toInitialCase = function() {
	return this[0].toUpperCase() + this.slice(1)
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
                assert: p => {
                    if (!r) throw Error.em("Is.judge",
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
            if ((i[0] === "_" || i === "judge") && ! i.startWith("_cor")) continue
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
        "-)":   ski.q("lt"),
        

        "le":   (x, a) => x <= a,
        "<=":   ski.q("le"),
        "-]":   ski.q("le"),
        
        "gt":   (x, a) => x > a,
        ">":    ski.q("gt"),
        "(+":   ski.q("gt"),

        "ge":   (x, a) => x >= a,
        ">=":   ski.q("ge"),
        "[+":   ski.q("ge"),

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
        (r, p, e) => {
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

function exTemplate(str, tem) {
    for (let n in tem) {
        const t = tem[n]
        if (Is.simple(t)) str = str.replace(RegExp(`(?<!\\\\)\\\${\\s*${n}\\s*}`, "g"), t)
        else if (Is.func(t)) {
            let r; while (r = str.match(RegExp(`(?<!\\\\)!{\\s*${n}([^]*?)\\s*}`))) {
                str = str.substring(0, r.index) +
                t(...(r[1].trim().split(/\s*(?<!\\)\|\s*/).slice(1))) +
                str.substring(r.index + r[0].length)
            }
        }
    }
    return str
}
exTemplate.reflect = processer => (str, tn, tem) => {
    const t = {}
    if (! tn.startWith("exT:")) tn = "exT:" + tn
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
    processer(exTemplate(str, t))
}

const Logger = o => ({
	opt: o ?? {},
	bind() {
		return bindo(this, /^(_|bind$)/)
	},
	_(s) { // Note: CSI.
		return this.opt.noColor ? "" : "\x1B[" + s
	}, 
    div(t, u, d) {
        process.stdout.write(
            "\n".repeat(u ?? 1) +
            "-".repeat(10) +
            "=".repeat(5) +
            (t ? " " +  this._("1;34m") + t + this._("0m") + " " : "") +
            "=".repeat(5) +
            "-".repeat(10) +
            "\n".repeat(d ?? 1)
        )
    },
    log(...m) {
        console.log(...m)
    },
    debug(...m) {
        if (this.opt.dirObj && m.length === 1 && Is.obj(m[0]))
            return console.dir(m[0], { depth: Infinity })
        if (this.opt.debug) console.log(...m)
    },
    warn(...m) {
        console.warn(this._("33m") + m.join(" ") + this._("0m"))
    },
    err(...m) {
		m = m.join(" ")
        if (this.opt.debug) throw m
        else {
			console.error(this._("31m") + m + this._("0m"))
			process.exit()
		}
    },
    errEOF(...m) {
        m = this._("31m") + m.join(" ") + this._("0m")
        if (this.opt.debug) throw m
        console.error(m)
        this.div("EOF", 1, 1)
        process.exit()
    },
    hili(m) {
        return this._("32m") + m  + this._("0m")
    },
	bold(m) {
		return this._("1m") + m + this._("0m")
	},
	table(t, pad) {
		return t.map(r => r.map((c, i) =>
			c + " ".repeat(pad[i] ? pad[i] - c.replace(/\x1B\[.+?m/g, "").length : 0)
		).join("")).join("\n")
	},
    code(m) {
        return m
            .replace(/^/mg, this._("48;5;158;32m"))
            .replace(/$/mg, this._("0m"))
    },
    exTemplateLog: exTemplate.reflect(console.log)
})

// :::: Ext     1v.1

Object.clone = src => {
    if (Is.judge(src, "any").simple().empty().re().q()) return src
    
    const res = Is.arr(src) ? [] : {}
    for (let i in src) res[i] = Object.clone(src[i])
    return res
}

// :::: Tool    lv.2

function serialize(src, opt) {
    return JSON.stringify(src, (k, v) => {
        if (opt?.regexp && Is.regexp(v)) return v.source
        return v
    }, opt.indent ?? 4)
}

const httpx = {
	get: (url, opt) => new Promise((resolve, reject) => {
		ski(url.match(/^(https?):\/{2}/)?.[1], { http, https }, ski.f(() => {
			reject(`Unknown protocol.\nURL: ${url}"`)
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
			res.on("end", async() => {
				let bf = bh.toBuffer()
				if (gzipped) bf = zlib.gunzipSync(bf)
				resolve(iconv.decode(bf, charset))
			})
		}).on("error", reject)
	})
}

// :: Export

module.exports = {
    EF,
    Is, Cc, ski,
    sleep, httpx, exTemplate, serialize,
    Logger
}

