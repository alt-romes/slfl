let highlighting = document.getElementById("highlighting")
let highlighting_content = document.getElementById("highlighting-content")
let editor = document.getElementById("editing")

update_code = (text) => {

    highlighting_content.innerHTML = text.replace(new RegExp("&", "g"), "&").replace(new RegExp("<", "g"), "<");
    Prism.highlightElement(highlighting_content)

}

this.proghistory = [];

back = () => {
    let newprog = proghistory.pop();
    editor.value = newprog
    update_code(newprog)
}

synth = (type, elem) => {
    let prog = editor.value;
    proghistory.push(prog)
    elem.disabled = true;
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
        elem.disabled = false;
    })
    //.catch(err => console.log("The error is " + err));
    console.log(prog);
}

displayErr = err => {

    let errdom = document.getElementById("error");

    if (err.includes("Parse"))
        err = "Failed to parse."

    errdom.innerHTML = err;
    errdom.hidden = false;

    setTimeout(() => {errdom.hidden = true}, 12000)

}

instructions = (instructions_val) => {

    let prog = editor.value;
    proghistory.push(prog)

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
lambdaId = (\\x -> x);

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

`

let maybe = `
data Maybe a = Nothing | Just a;

data List a = Nil | Cons (a * List a);


synth return :: a -o Maybe a;

synth empty :: Maybe a;

synth bind :: Maybe a -o (a -o Maybe b) -> Maybe b;

synth maybe :: b -> (a -o b) -> Maybe a -o b;

`

let list = `
data List a = Nil | Cons (a * List a);

data Maybe a = Nothing | Just a;


synth singleton :: a -o List a;

synth append :: List a -o List a -o List a;

synth map :: (!(a -o b)) -o List a -o List b;

synth foldl :: !(b -o a -o b) -o b -o List a -o b | choose 1;

synth uncons :: List a -o Maybe (a * List a);

synth foldr :: !(a -o b -o b) -o b -o List a -o b;

synth insert :: a -o List a -o List a;

synth concat :: List (List a) -o List a;

`

let array = `

newMArray :: Int -> (MArray a -o !b) -o b;

write :: MArray a -o (Int * a) -> MArray a;

freeze :: MArray a -o !(Array a);

foldl :: (a -o b -o a) -> a -o (List b) -o a;

#read :: (MArray a -o Int -> (MArray a * !a));

synth array :: Int -> List (!(Int * a)) -> Array a | using (foldl) | depth 3;

`

let misc = `
data List a = Nil | Cons (a * List a);
data Bool = False | True;


synth reverse :: List a -o List a -o List a
  | assert
  (reverse (Cons (1, Cons (2, Nil))) Nil) == (Cons (2, Cons (1, Nil)));

t = 2;

main = case (4 + 3 + t == t + 7) => 4 < t of
         True -> False
        | False -> True;
`
