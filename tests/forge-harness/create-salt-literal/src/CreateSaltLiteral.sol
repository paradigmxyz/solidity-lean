// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// CREATE-SALT-LITERAL (gap #112) — the `new C{salt: e}(…)` salt option accepts
// any value IMPLICITLY CONVERTIBLE to bytes32, not only a value already typed
// bytes32. Per solc RationalNumberType::isImplicitlyConvertibleTo an untyped
// number literal converts to bytes32 iff its value is 0 OR it is an exact
// 32-byte hex literal. solidity-lean formerly over-rejected the whole contract
// because the salt-option checker used a strict bytes32 equality that an
// untyped literal (whose type is a rational/number literal) could never meet.
// Pinned solc 0.8.35 ACCEPTS `salt: 0` and `salt: <32-byte hex>` and REJECTS a
// nonzero non-width literal such as `salt: 5`.
contract Deployed {
    uint256 public seed;

    constructor(uint256 s) payable {
        seed = s;
    }
}

contract SaltLiteralFactory {
    // integer literal 0 as salt
    function makeZeroSalt(uint256 s) external returns (Deployed) {
        return new Deployed{salt: 0}(s);
    }

    // exact 32-byte hex literal as salt
    function makeHexSalt(uint256 s) external returns (Deployed) {
        return
            new Deployed{
                salt: 0x0000000000000000000000000000000000000000000000000000000000000001
            }(s);
    }

    // Two DIFFERENT salt literals deployed by the same factory land at DIFFERENT
    // CREATE2 addresses, and each deployed contract's constructor ran (seed set).
    function deployBothReadSeeds(uint256 s)
        external
        returns (uint256 zeroSeed, uint256 hexSeed, bool differentAddresses)
    {
        Deployed a = new Deployed{salt: 0}(s);
        Deployed b =
            new Deployed{
                salt: 0x0000000000000000000000000000000000000000000000000000000000000001
            }(s + 1);
        zeroSeed = a.seed();
        hexSeed = b.seed();
        differentAddresses = address(a) != address(b);
    }
}
