let highlighting = document.getElementById("highlighting")
let highlighting_content = document.getElementById("highlighting-content")
let editor = document.getElementById("editing")

update_code = (text) => {

    highlighting_content.innerHTML = text.replace(new RegExp("&", "g"), "&").replace(new RegExp("<", "g"), "<");
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

instructions = (instructions_val) => {

    editor.value = instructions_val
    update_code(instructions_val)
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
        update_code(elem.value)

        // Move cursor
        elem.selectionStart = cursor_pos
        elem.selectionEnd = cursor_pos
    }

}



let simple_typing = `# Basics
# -- Press the button "type" to generate type annotations!


# -- natural number
n = 42;

# -- variable
identity x = x;

# -- lambda
lambdaId = (\\x -o x);

# -- function application
superId x = identity lambdaId x;

# -- tensor value
tensor x y = (x, y);

# -- let tensor value
tensorId tensor = let x*y = tensor in (x, y);

# -- unit value
unit = ();

# -- let unit
seqc unit next = let _ = unit in next;

# -- with value
with a = (a | a);

# -- deconstruct with
first with = fst with;
second with = snd with;

# -- plus value
inleft a = inl a;
inright a = inr a;

# -- case of plus
caseofplus x =
    case x of
        inl a -> a
      | inr b -> b;

# -- bang value
bang = ! 8;

# -- use unrestricted banged value
usebang bangValue expr = let !value = bangValue in expr value;

# -- let in
letfour a = let c = 4 in a c;


# -- marks are used to indicate we want the expression to be synthed from the type
getId = {{ (a -o a) }};

# -- sum value
# semaph = union { red : Num; green : Num; yellow Zero; };

# -- case of sum
# casesem sem = case sum sem of
#                 red x -> x
#                 | green y -> y;

`

let simple_synth = `data Bool = True | False;

data Num = Zero | Succ Num;


synth predecessor :: (Num -o Num);

synth rec recToZero :: (Num -o Num);

main :: (Num -o (Bool -o Num));
main num cond = case cond of
      True -> predecessor num
    | False -> recToZero num;

`

let lambda_synth = `data Expr = Var Nat | Lambda (Nat * Expr) | App (Expr * Expr);


synth value :: (Expr -o Nat);
`
