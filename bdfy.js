// :: Import

const http = require('http')
const qs = require('querystring')
const crypto = require("crypto")

// :: Config

const bf = {
    APPID:  "*****************",
    secret: "********************",
    addr:   "http://api.fanyi.baidu.com/api/trans/vip/translate"
}

// :: API

function translate(q, from, to) {
    q = q.toString() // TODO: UTF-8

    const salt = parseInt(Math.random() * 10_000)
    const md5 = crypto.createHash("md5")
    const sign = md5.update(bf.APPID + q + salt + bf.secret).digest("hex")

    return new Promise((resolve, reject) => {
        http.get(bf.addr + "?" + qs.stringify(
            { q, from, to, appid: bf.APPID, salt, sign }
        ), res => {
            const { statusCode } = res
            const contentType = res.headers['content-type']

            let error
            if (statusCode !== 200)
                error = new Error('Request Failed.\n' + `Status Code: ${statusCode}`)
            else if (!/^application\/json/.test(contentType))
                error = new Error('Invalid content-type.\n' + `Expected application/json but received ${contentType}`)
            if (error) {
                res.resume()
                reject(error)
            }

            let data = ""
            res.setEncoding('utf8')
            res.on("data", chunk => data += chunk)
            res.on("end", () => resolve(data))
        })
    })
}

// :: Export

module.exports = { translate }

