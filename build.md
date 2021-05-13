
I guess one of the main questions is how the building pipeline is going to look like. I want to control the whole build process with nix. Still, I don't like planning this stuff in too too much detail, as it just makes me anxious. I should just do *something*.

1) *Scanning*. The nice thing is that this doesn't need a vocabulary, so we can scan all files in parallel without needing to care about the order. Thus the scanning capabilities need to be completely exposed to the commandline. The scanning process should also scan for aliased vocabulary or vocabulary imported from other `.lean.tex` files. Thus every file will have its custom set of dependencies. Each file's new, added vocabular will be modelled as a nix package that is stored in the nix store.

Simply put, the scanning will work by generating corresponding 'tasks'(or 'small packages') for nix. I guess one can learn a lot from the way lean handles this. Since lean has a package for each `.olean` file.

This process outputs a `scan_result.json` and a `imports.json`. The imports will be processed in 3) later.

2) *Parsing*. Once the correct vocabulary has been built by nix, the parser can read it and build it and serialize it into an appropriate `.json` file. This is another nix 'task'.

3) *Logics*. Here we call my custom lean package in order to generate `.olean` objects.

The source code for all these tools should be in the same repo and exposed via the command line in order to be made into nix flake functions.

---

Actually, I want to encode patterns into `.olean` files, such that they can be reconstructed. So before running the parser on a new `.lean.tex` file, the environment must be constructed from its dependencies. After the environment is constructed, one simply needs to reconstruct the pattern information.

This will likely require adding very custom attributes, not sure that this works well. Actually, one could encode things like associativity by a clever naming scheme, it should not be too bad. Otherwise one can encode the information in hexadecimal and append like 2-4 hexadecimal digits. That should be able to store a huge amount of information.

In order for editor support to work, one might have to fork the nix build pipeline repo for lean.

Note that scanning can still be done in parallel, thus at quite a low cost.

---

## Some notes on how lean 4 building works

### Packages and their attributes

The `buildLeanPackage` function (defined in lean 4's `nix/buildLeanPackage`) that is called in `flake.nix` of each project takes as argument all necessary things to construct the package. E.g. source code, name and dependencies. (For an example with dependencies, see this
https://github.com/Kha/testpkg2/blob/master/flake.nix#L5
)

The output contains developer tools like

* `vscode-dev`
* `emacs-dev`
* `lean-dev` is simply a wrapper around the `lean` executable provided by the flake at `github:leanprover/lean4`
* `leanpkg-dev` is also looks like just a wrapper around a `leanpkg` executable.
* `lean-bin-dev` is a wrapper around the previous two tools. The lean docs [here](https://leanprover.github.io/lean4/doc/setup.html) recommend using this for manually pointing vscode to the leanpkgs and lean executables, in case the `vscode-dev` or `emacs-dev` components do not satisfy your needs.

Presumably this `lean` executable is simply the `defaultPackage` attribute in lean 4's `flake.nix`. This points to a lean 4's `nix/packages.nix`, which points to `nix/bootstrap.nix`.

But I think that these dev things are besides the point. Lets go back to `nix/buildLeanPackage.nix`. (Note the nice `substituteAll` attribute, this seems like an elegant way to do runtime dependencies. One could use that for eprover in `zf`). I think the most important part is the `lean-package` attribute.

Running `nix build .#lean-package -o lean-package` for your project will produce a custom lean executable that has your project builtin as a library ready to be imported. Pointing to your project seems to work by setting the `LEAN_SRC_PATH` and `LEAN_PATH` environment varibles, so is is nice and transparent.

The `nix/buildLeanPackage.nix` file also contains various other derivations:
* C source code `cTree`
* C object files `oTree`
* lean object files `modRoot`

### Building modules inside a package

It seems like this is again based on the `LEAN_PATH` environment variable. Thus one might have hope of writing a straightforward modification/overlay of our nix flake. It seems like the key thing would be overriding the `lean` executable to instead point to a shell script with a dumbed-down `lean` command of my own, that runs Adrian's parser and my logic processing when required.
