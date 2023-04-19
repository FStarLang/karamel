{
  inputs = {
    fstar.url = "github:fstarlang/fstar";
    flake-utils.follows = "fstar/flake-utils";
    nixpkgs.follows = "fstar/nixpkgs";
  };

  outputs = { self, fstar, flake-utils, nixpkgs }:
    flake-utils.lib.eachSystem [ "x86_64-linux" ] (system:
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
