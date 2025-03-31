
=== Installing agda-prelude ===

To run the lecture code you need the `agda-prelude` library.

Download it from github or clone it using git (in some suitable location):

```
git clone https://github.com/UlfNorell/agda-prelude
```

The `master` branch of `agda-prelude` works with Agda version 2.6.3. If you are working with
(the unreleased) Agda version 2.6.4 you need the `dev` branch, and if you have an older version of
Agda you need the corresponding `compat-*` branch of `agda-prelude`. For
instance, `compat-2.6.2` for Agda version 2.6.2.x:

```
$ agda --version
Agda version 2.6.2.2
```

Then go into the directory where you cloned `agda-prelude` and switch branch to
the appropriate `compat-X.Y.Z` branch (only the first three digits of the
version number):

```
$ cd agda-prelude
$ git checkout compat-2.6.2
```

Add a line with the full path to `agda-prelude.agda-lib` to `~/.agda/libraries`
(or `C:\Users\USERNAME\AppData\Roaming\agda\libraries` on Windows, see [1] for more
information). Create the directory and the file if they don't exist. Once you've
done this your `~/.agda/libraries` file should look something like this:

```
/path/to/stdlib/standard-library.agda-lib
/path/to/prelude/agda-prelude.agda-lib
```

Once these are in place you should be able to load the files from the lecture and
Agda will find the `agda-prelude` library code.

To use `agda-prelude` (or the standard library) for your own code you can write your
own `.agda-lib` file. See `lecture11.agda-lib` (and [1]) for what it should look like.

* [1] https://agda.readthedocs.io/en/v2.6.2/tools/package-system.html

=== Compiling and running the code ===

To compile the code you can load Main.agda in Emacs and hit `C-c C-x C-c` or choose
"Compile" from the "Agda" menu. You can also compile from the command line using

```
agda -c Main.agda
```

Either method produces a binary `Main` (or `Main.exe`) that you can call from the
command line with a `.lam` file and some arguments. For instance,

```
$ ./Main factorial.lam 5
Type: nat
Term: (λ (plus : nat → nat → nat) → (λ (times : nat → nat → nat) → (λ (fac : nat → nat) → fac) (natrec nat 1 (λ (n : nat) → tim
es (suc n)))) (λ (n : nat) → natrec nat 0 (λ (_ : nat) → plus n))) (λ (n : nat) → natrec nat n (λ (_ : nat) → suc)) 5
Val:  120
```
