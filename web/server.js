const http = require("http");
const fs = require("fs");
const tmp = require("tmp");
const execSync = require("child_process").execSync;

const port = 25565;

// Remove all controlled temporary objects on process exit
tmp.setGracefulCleanup();

const server = http.createServer(function (req, res) {

    if (req.method == "GET")
        fs.readFile(__dirname + "/index.html", (err, data) => {

            if (err) {
                res.writeHead(500);
                res.end(err);
                return;
            }

            res.setHeader("Content-Type", "text/html");
            res.writeHead(200);
            res.end(data);
        });
    else if (req.method == "POST") {

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
                pout = "" + execSync("/usr/bin/env STLLC complete " + tmpf.name);
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