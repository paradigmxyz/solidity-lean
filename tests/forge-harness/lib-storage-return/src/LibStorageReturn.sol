// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// #155 LIB-STORAGE-RETURN — solc 0.8.35 ACCEPTS public/external LIBRARY
// functions that RETURN a storage reference or a mapping type, symmetric with
// library functions that TAKE storage/mapping parameters (already accepted,
// #90/#93). The model formerly over-rejected the return case. This library
// declares exactly the over-rejected headers: a public function returning a
// struct-storage reference, an external one, and public/external functions
// returning a `mapping(...) storage`. Importing this unit into the Lean
// checker must ACCEPT (the acceptance regression guard).
library L {
    struct S { uint256 x; }
    struct D { mapping(uint256 => uint256) m; }

    // returns (S storage) — over-rejected header, public.
    function refPublic(S storage s) public view returns (S storage) {
        return s;
    }

    // returns (S storage) — over-rejected header, external.
    function refExternal(S storage s) external view returns (S storage) {
        return s;
    }

    // returns (mapping(uint=>uint) storage) — over-rejected header, public.
    function mapPublic(D storage d) public view returns (mapping(uint256 => uint256) storage) {
        return d.m;
    }
}
