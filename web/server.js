const http = require("http");
const fs = require("fs");
const tmp = require("tmp");
const execSync = require("child_process").execSync;

const port = 25565;

// Remove all controlled temporary objects on process exit
tmp.setGracefulCleanup();

const server = http.createServer(function (req, res) {

    if (req.method == "GET") {

        console.log("GET " + req.url)
        // Return the requested resource
        if (req.url == "/" || req.url == "/index.html")
            returnFile("/index.html", "text/html", res)

        else if (req.url == "/style.css")
            returnFile("/style.css", "text/css", res)

        else if (req.url == "/main.js")
            returnFile("/main.js", "application/javascript", res)

    }
    else if (req.method == "POST") {

        console.log("POST " + req.url)
        
        let type = "error"
        if (req.url == "/synth")
            type = "complete"
        if (req.url == "/type")
            type = "type"

        res.setHeader("Content-Type", "application/json");

        var body = ""; // Read data into body until finished, then execute callback
        req.on("data", chunk => {
            body += chunk;
        });

        req.on("end", () => {

            // Synthetize program marks and return full program

            // Write body to tmp file
            const tmpf = tmp.fileSync();
            fs.writeSync(tmpf.fd, body);

            console.log("Body:\n" + body);
            
            var pout;
            try {
                pout = "" + execSync("/usr/bin/env timeout 3s STLLC " + type + " " + tmpf.name);
            }
            catch (err) {
                
                err = err.toString();
                err = err.substring(err.indexOf("\n") + 1);  // Remove node error
                err = err.replace(` "`+ tmpf.name + `"`, "");      // Remove tmpfile name
                
                res.writeHead(400);
                res.end(JSON.stringify({result: null, error: err}));

                return;
            }
            
            console.log("Synthetized: " + pout);

            res.writeHead(200);
            res.end(JSON.stringify({result: pout, error: null}));
        });
    }

}).listen(port);


returnFile = (name, content_type, res) => {

    fs.readFile(__dirname + name, (err, data) => {

        if (err) {
            res.writeHead(500);
            res.end(err);
            return;
        }

        res.setHeader("Content-Type", content_type);
        res.writeHead(200);
        res.end(data);
    });

}
