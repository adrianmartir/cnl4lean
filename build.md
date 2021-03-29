
I guess one of the main questions is how the building pipeline is going to look like. I want to control the whole build process with nix. Still, I don't like planning this stuff in too too much detail, as it just makes me anxious. I should just do *something*.

1) *Scanning*. The nice thing is that this doesn't need a vocabulary, so we can scan all files in parallel without needing to care about the order. Thus the scanning capabilities need to be completely exposed to the commandline. The scanning process should also scan for aliased vocabulary or vocabulary imported from other `.lean.tex` files. Thus every file will have its custom set of dependencies. Each file's new, added vocabular will be modelled as a nix package that is stored in the nix store.

Simply put, the scanning will work by generating corresponding 'tasks'(or 'small packages') for nix. I guess one can learn a lot from the way lean handles this. Since lean has a package for each `.olean` file.

This process outputs a `scan_result.json` and a `imports.json`. The imports will be processed in 3) later.

2) *Parsing*. Once the correct vocabulary has been built by nix, the parser can read it and build it and serialize it into an appropriate `.json` file. This is another nix 'task'.

3) *Logics*. Here we call my custom lean package in order to generate `.olean` objects.

The source code for all these tools should be in the same repo and exposed via the command line in order to be made into nix flake functions.
