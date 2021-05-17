# I have no fucking clue why, but `nix-direnv` fails when evaluating this flake with the bizarre error
# "unable to download 'https://api.github.com/repos/leanprover/lean4/tarball/0000000000000000000000000000000000000000': HTTP error 404".
# Evaluating with `nix build` or `nix develop` works normally, though.
# But actually, nobody cares since I am not building anything from a custom command line
# TODO: This should be renamed to `readable-lean` as it best expresses the intent of the project
{
  description = "CNL for lean";

  inputs.lean.url = github:leanprover/lean4;
  inputs.flake-utils.url = github:numtide/flake-utils;
  # Should require a fork of Adrian's zf.

  outputs = { self, lean, flake-utils }: flake-utils.lib.eachDefaultSystem (system:
    let
      leanPkgs = lean.packages.${system};
      pkg = leanPkgs.buildLeanPackage {
        name = "ReadableLean";  # must match the name of the top-level .lean file
        src = ./.;
        executableName = "rlean";
        linkFlags = ["-rdynamic"];
      };
    in {
      packages = pkg // {
        inherit (leanPkgs) lean;
      };

      defaultPackage = pkg.modRoot;
    });
}
