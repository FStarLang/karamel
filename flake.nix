{
  inputs = {
    # Pin to fstar1 for the legacy Low* libraries required by krmllib.
    fstar.url = "github:fstarlang/fstar/019f4e3e38531387ea8534b587aaa23b685edeb5";
    flake-utils.follows = "fstar/flake-utils";
    nixpkgs.follows = "fstar/nixpkgs";
  };

  outputs = { self, fstar, flake-utils, nixpkgs }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        fstarPackages = fstar.packages.${system};
        pkgs = import nixpkgs { inherit system; };
        karamel = pkgs.callPackage ./.nix/karamel.nix {
          inherit (fstarPackages) fstar ocamlPackages z3;
          version = self.rev or "dirty";
        };
      in {
        packages = {
          inherit karamel;
          default = karamel;
        };
      });
}
