// :: Info
//    NAME      ForkKILLET's Utilities (fkutil)
//    AUTHOR    ForkKILLET

// :: Main

// :::: Ext     lv.0

Error.em = (title, msg) => Error(`\x1B[31m[${title}] ${msg}\x1B[0m`)
Error.unreachable = () => Error.em("???", "It's unreachable! You can never see this f**king error!")

Date.prototype.fommat = function(f, UTC) {
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

String.prototype.startWith = function(s) { return this.indexOf(s) === 0 }

// :::: Tool    lv.0

function callW(f) { return (...p) => f(...p) }

function keyOf(key, src, dftKey) {
    let v = (src ? src[key] : null) ?? src[dftKey]
    if (typeof v !== "object" || v === null) return v
    if (v._keyQuote && typeof v.k === "string") return keyOf(v.k, src, dftKey)
}
keyOf.q = k => ({ k, _keyQuote: true })

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

    // :::::: judge mode

    judge       = (x, rule, final) => {
        if (! this.func(rule)) {
            rule = keyOf(rule, {
                any:    (r, p) => ({ pass: p || r, forcepass: r }),
                anyway: (r, p) => ({ pass: p || r, forcepass: r === "forcepass" }),
                all:    (r, p) => ({ pass: (p || p === null) && r, forcepass: r === "forcepass" }),
                none:   (r, p) => ({ pass: (p || p === null) && !r, forcepass: false })
            }, "all")
        }
        if (! this.func(final)) {
            final = keyOf(final, {
                assert: p => {
                    if (!r) throw Error.em("Is.judge",
                        `Assert failed; Rule: ${rule}; More assert info: see Cc.`)
                    return true
                },
                result: p => p
            }, "result")
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

    compare     = (x, op, a, b) => keyOf(op, {
        "lt":   (x, a) => x < a,
        "<":    keyOf.q("lt"),
        "-)":   keyOf.q("lt"),
        

        "le":   (x, a) => x <= a,
        "<=":   keyOf.q("le"),
        "-]":   keyOf.q("le"),
        
        "gt":   (x, a) => x > a,
        ">":    keyOf.q("gt"),
        "(+":   keyOf.q("gt"),

        "ge":   (x, a) => x >= a,
        ">=":   keyOf.q("ge"),
        "[+":   keyOf.q("ge"),

        "ltgt": (x, a, b) => a < x && x < b,
        "in":   keyOf.q("ltgt"),
        "<<":   keyOf.q("ltgt"),
        "()":   keyOf.q("ltgt"),

        "legt": (x, a, b) => a <= x && x < b,
        "<=<":   keyOf.q("legt"),
        "[)":   keyOf.q("legt"),

        "ltge": (x, a, b) => a < x && x <= b,
        "<<=":   keyOf.q("ltge"),
        "(]":   keyOf.q("ltge"),

        "lege": (x, a, b) => a <= x && x <= b,
        "IN":   keyOf.q("lege"),
        "<=<=": keyOf.q("lege"),
        "[]":   keyOf.q("lege"),
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

    objectR     = x => this.object(x) && ! this.nul(x)
    objR        = this.objectR

    // :::::: about array

    among       = (x, ...arr) => arr.flat().includes(x)

    // :::::: forcepass

    _w_able     = f => (...p) => f(p) ? "forcepass" : true

    nullable    = this._w_able(this.empty)
    eqable      = this._w_able(this.eq)
    amongable   = this._w_able(this.among)

    // :::::: correcter

    _corV       = v => ({ _cor: v, _corT: this._corT })

    smartype    = (x, t) => {
        if (this.type(x, t)) return true
        if ((t === "undefined" || t === "null") && x == null) return this._corV(eval(t))
        if (t === "number" && this.numstr(x)) return this._corV(Number(x))
        if (t === "string" && x?.toString) return this._corV(x.toString())
    }
}
const Is = new _c_Is()

function Cc(x, n) {
    const cs = [], xd = () => x
    xd._judge = true
    const IsJ = Is.judge(xd,
        (r, p, e) => {
            cs.push(e)
            if (r) return { pass: true, forcepass: r === "forcepass" }
            if (r._corT === IsJ._corT) x = r._cor
            throw Error.em("Cc",
                `Checkee ${n} requires ${e.name}${e.param?.length ? " " + e.param : ""}, but got ${x}.`
            ) // TODO: dull work
        },
        () => x
    )
    IsJ._corT = Math.random()
    Object.defineProperty(IsJ, "r", {
        get() { return IsJ.q() }
    })
    return IsJ
}

// :::: Ext     1v.1

Object.clone = src => {
    if (Is.judge(src, "any").num().str().fun().bigint().empty().re().q()) return src
    
    const res = Is.arr(src) ? [] : {}
    for (let i in src) res[i] = Object.clone(src[i])
    return res
}

// :::: Tool    lv.2

const EF = () => {}

async function ajax(tar, encode = "utf8", http_) {
   return new Promise((resolve, reject) => {
        (http_ ?? require("http")).get(tar, res => {
            const { statusCode } = res
            const contentType = res.headers['content-type']

            if (statusCode !== 200) {
                res.resume()
                reject(new Error(`ajax: Request failed.\n` +
                    `Status Code: ${statusCode}\n` +
                    `URL: ${tar}`
                ))
            }

            let data = ""
            res.setEncoding(encode)
            res.on("data", chunk => data += chunk)
            res.on("end", () => resolve(data))
        })
    })
}

// :: Export

module.exports = {
    EF, Is, Cc,
    callW, keyOf,
    ajax
}

