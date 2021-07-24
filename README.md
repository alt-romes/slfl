# SILI - Synthesis of Functional Linear Programs

SILI is a program synthesizer that generates linear programs from type-based specifications:

Given the following program written in the *SILI* language:
```hs
data List a = Nil | Cons (a * List a);
synth map :: (a -o b) -> (List a -o List b);
```
*SILI* will synthesize and output:
```hs
map c d = let !e = c in
  case d of
      Nil -> Nil
    | Cons f ->
        let g*h = f in
          Cons (e g, map (!e) h);
```

## How to use

The *SILI* language is similar to haskell, despite some variations in the syntax.
The main differences come from the linear types.

A linear function `a -o b` is a function whose argument is used **linearly** (i.e. *exactly once*) in its body:
```hs
id :: a -o a;
id a = a;
```

To use a multiplicative pair `(a * b)` linearly, both `a` and `b` must be used linearly:
```hs
curry :: ((a * b) -o c) -o (a -o b -o c);
curry f = \x -> \y -> f (x, y);
```

A resource might be used non-linearly by use of the exponential connective `!`.
For example, the function `!a -o b` might use `a` any amount of times (0..n) in its body after consuming `!a`.
```hs
let dup :: !a -o (a * a);
dup x = let !y = x in (y, y);
```
The function type with an unrestricted parameter can be written `a -> b`, that is, `!a -o b` is equal to `a -> b`.

...

To mark a function for synthesis, write the keyword `synth` before its type annotation:
```hs
data Maybe a = Nothing | Just a;
synth return :: a -o Maybe a;
```

Additional keywords may be used to better guide the process...

Choose -- selects a different synthesized program. Will fail if choice is higher than the number of available programs
```hs
data List a = Nil | Cons (a * List a);

synth foldl :: (b -o a -o b) -> b -o List a -o b | choose 1;
```

Assert -- asserts a predicate where the function being synthesized can be used
```hs
data List a = Nil | Cons (a * List a);

synth singleton :: a -o List a;

synth reverse :: List a -o List a
    | assert reverse (Cons (1, singleton 2)) == Cons (2, singleton 1);
```

Using -- force a function (or ADT constructor) to be in the resulting program's body.
Depth -- allow for a deeper search -- might find more results, but might also become too slow.
```hs
newMArray :: Int -> (MArray a -o !b) -o b;

write :: MArray a -o (Int * a) -> MArray a;

freeze :: MArray a -o !(Array a);

foldl :: (a -o b -o a) -> a -o (List b) -o a;

synth array :: Int -> List (!(Int * a)) -> Array a | using (foldl) | depth 3;
```


### On the web

A live demonstration is on (*comming soon*). Try some example programs, or write your own, to see *SILI* in action.
The web interface allows you to typecheck, synthesize functions marked with `synth`, and evaluate programs.

### From your terminal

A program file in the *SILI* language typically uses the haskell extension `.hs` because the syntax is similar and 
it means syntax-highlighting comes "for free".
To pass a program to *SILI*, run `STLLC` (to be changed...) followed by the action and the program file.

* Parse: `STLLC parse prog.hs`

* Typecheck: `STLLC type prog.hs`

* Synthesize: `STLLC complete prog.hs`

* Evaluate: `STLLC eval prog.hs`


### From vim

Future work... :)

## Compiling from source

*SILI* is built using Cabal. First, install the package `cabal-install` from your system's package manager.

Secondly, `git clone` this repository, and `cd` to the directory `STLLC`, and run
```sh
cabal install
```
to build and install `SILI` (currently named `STLLC`) to your `~/.cabal/bin` directory.
To use `SILI` from anywhere on the command line, add the directory to your `PATH`.

...

## Web server

After having STLLC installed, to start the web server, `cd` to the directory `web` and run
```
node server.js
```

The web interface should now be live at `https://localhost:25565`

## Testing

[How to test](https://github.com/alt-romes/slfl/blob/master/STLC/tests/how-to-test.md)
