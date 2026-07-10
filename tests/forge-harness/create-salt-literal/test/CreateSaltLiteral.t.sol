// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {SaltLiteralFactory, Deployed} from "../src/CreateSaltLiteral.sol";

/// Ground-truth (solc 0.8.35 / Foundry EVM) for the CREATE-SALT-LITERAL gap
/// (#112): `new C{salt: <literal>}(…)` where the salt is an untyped literal
/// implicitly convertible to bytes32 (`0` or a 32-byte hex literal).
contract CreateSaltLiteralForgeTest {
    function testZeroSaltDeploys() public {
        SaltLiteralFactory f = new SaltLiteralFactory();
        Deployed d = f.makeZeroSalt(7);
        require(d.seed() == 7, "zero-salt constructor ran");
    }

    function testHexSaltDeploys() public {
        SaltLiteralFactory f = new SaltLiteralFactory();
        Deployed d = f.makeHexSalt(9);
        require(d.seed() == 9, "hex-salt constructor ran");
    }

    function testDifferentSaltsDifferentAddresses() public {
        SaltLiteralFactory f = new SaltLiteralFactory();
        (uint256 zeroSeed, uint256 hexSeed, bool different) =
            f.deployBothReadSeeds(11);
        require(zeroSeed == 11, "zero-salt seed");
        require(hexSeed == 12, "hex-salt seed");
        require(different, "distinct salts -> distinct CREATE2 addresses");
    }
}
