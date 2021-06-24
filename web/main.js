let highlighting = document.getElementById("highlighting")
let highlighting_content = document.getElementById("highlighting-content")
let editor = document.getElementById("editing")

update_code = (text) => {

    highlighting_content.innerText = text
    Prism.highlightElement(highlighting_content)

}

synth = (type) => {
    let prog = editor.value;
    fetch(type, {
        method: "POST",
        body: prog,
        headers: {
            'Content-Type': 'application/json'
        }
    })
    .then(response => response.json())
    .then(data => {
        console.log(data);
        if (data.result == null)
            displayErr(data.error)
        else {
            editor.value = data.result
            update_code(data.result)
        }    
    })
    //.catch(err => console.log("The error is " + err));
    console.log(prog);
}

displayErr = err => {

    let errdom = document.getElementById("error");
    errdom.innerHTML = err;
    errdom.hidden = false;

    setTimeout(() => {errdom.hidden = true}, 12000)

}

sync_scroll = elem => { highlighting.scrollTop = elem.scrollTop }

check_tab = (elem, event) => {
    // Capture tab as input key
    if (event.key == "Tab") {
        event.preventDefault() // Ignore default tab action
        let code = elem.value
        let before_tab = code.slice(0, elem.selectionStart) // Text before tab
        let after_tab = code.slice(elem.selectionEnd, elem.value.length) // Text after tab
        let cursor_pos = elem.selectionEnd + 4; // Cursor moves 4 spaces
        elem.value = before_tab + "    " + after_tab // Add tab between content

        // Move cursor
        elem.selectionStart = cursor_pos
        elem.selectionEnd = cursor_pos
    }

}

