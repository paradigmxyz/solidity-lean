// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

/// TYPE-BLIND ARITY-FALLBACK CLOSURE: same-arity library overloads where the
/// WRONG candidate is declared FIRST. The importer's arity fallbacks (used
/// when the exact shape gate does not model an argument) previously bound the
/// first same-arity candidate type-blindly; the `arityFallbackCompatible`
/// filter must exclude the declared-first overload whose known param type
/// definitely mismatches the argument, binding like solc. Probes both the
/// using-for attached-receiver path and the intra-library helper-call path.
library AttachLib {
    struct Box {
        uint256 v;
    }

    // WRONG candidate for a Box argument, declared FIRST (same arity).
    function scale(uint256 self, uint256 m) internal pure returns (uint256) {
        return self * m;
    }

    function scale(uint256 self, Box memory b) internal pure returns (uint256) {
        return self + b.v;
    }
}

library HelperLib {
    struct Pair {
        uint256 a;
        uint256 b;
    }

    // WRONG candidate for a Pair argument, declared FIRST (same arity).
    function comb(uint256 x, uint256 k) internal pure returns (uint256) {
        return x * 1000 + k;
    }

    function comb(Pair memory p, uint256 k) internal pure returns (uint256) {
        return p.a + p.b + k;
    }

    // Intra-library call site: overloaded helper resolved inside the library.
    function driver(uint256 seed) internal pure returns (uint256) {
        Pair memory p = Pair(seed, 5);
        return comb(p, 7);
    }

    function driverUint(uint256 seed) internal pure returns (uint256) {
        return comb(seed, 7);
    }
}

contract ArityOverloadBinding {
    using AttachLib for uint256;

    // Attached call whose argument is a struct: must bind scale(uint256,Box)
    // (the SECOND same-arity candidate), not the declared-first uint overload.
    function attachedBox(uint256 x) external pure returns (uint256) {
        AttachLib.Box memory b = AttachLib.Box(3);
        return x.scale(b); // x + 3
    }

    // Attached call whose argument is a uint: binds the uint overload.
    function attachedUint(uint256 x) external pure returns (uint256) {
        return x.scale(4); // x * 4
    }

    // Intra-library overloaded helper, struct argument: comb(Pair,uint256)
    // -> seed + 5 + 7.
    function libDriver(uint256 seed) external pure returns (uint256) {
        return HelperLib.driver(seed);
    }

    // Intra-library overloaded helper, uint argument: comb(uint256,uint256)
    // -> seed * 1000 + 7.
    function libDriverUint(uint256 seed) external pure returns (uint256) {
        return HelperLib.driverUint(seed);
    }
}
