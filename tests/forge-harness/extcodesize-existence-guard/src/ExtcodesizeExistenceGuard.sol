// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

interface IPoke {
    function poke() external;
}

contract PokeTarget is IPoke {
    uint256 public pokes;

    function poke() external {
        pokes += 1;
    }
}

contract ExtcodesizeGuardCaller {
    mapping(uint256 => IPoke) public registry;

    // A1 -- try over a possibly-codeless address, void call, no `returns`
    // clause.  solc (v0.8.35) emits the `extcodesize` existence guard BEFORE
    // the CALL opcode, so a codeless target reverts the caller UNCATCHABLY:
    // the `catch` clause can never run and this function reverts the whole tx.
    // With a real code-bearing target the call succeeds and this returns 1.
    function tryPoke(address a) external returns (uint256) {
        try IPoke(a).poke() {
            return 1;
        } catch {
            return 2;
        }
    }

    // A3 -- void external call through a mapping-index receiver
    // (`registry[key]`, not an `ident` / `C(x)` receiver).  The existence
    // guard must still fire, so a codeless registered target reverts here too.
    function pokeViaMapping(uint256 key, IPoke t) external {
        registry[key] = t;
        registry[key].poke();
    }
}
