// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import "../src/ExtcodesizeExistenceGuard.sol";

contract ExtcodesizeGuardForgeTest {
    // A codeless address: never deployed, so extcodesize == 0.
    address constant EOA = address(0xBEEF);

    // A1 -- try over a codeless address reverts the caller UNCATCHABLY: the
    // extcodesize guard runs before the CALL, so the `catch` clause (which
    // would otherwise return 2) never runs and the whole tx reverts.
    function testTryOverCodelessRevertsUncatchably() public {
        ExtcodesizeGuardCaller caller = new ExtcodesizeGuardCaller();
        (bool ok, ) = address(caller).call(
            abi.encodeWithSelector(caller.tryPoke.selector, EOA)
        );
        require(!ok, "try over a codeless address must revert (uncatchable)");
    }

    // A1 control -- a code-bearing target succeeds and the try body returns 1.
    function testTryOverCodeReturnsOne() public {
        ExtcodesizeGuardCaller caller = new ExtcodesizeGuardCaller();
        PokeTarget target = new PokeTarget();
        require(caller.tryPoke(address(target)) == 1, "try over code returns 1");
    }

    // A3 -- a void external call through a mapping-index receiver still hits the
    // existence guard, so a codeless registered target reverts.
    function testMappingReceiverOverCodelessReverts() public {
        ExtcodesizeGuardCaller caller = new ExtcodesizeGuardCaller();
        (bool ok, ) = address(caller).call(
            abi.encodeWithSelector(
                caller.pokeViaMapping.selector,
                uint256(7),
                IPoke(EOA)
            )
        );
        require(!ok, "mapping-receiver call over codeless target must revert");
    }

    // A3 control -- with a code-bearing target the mapping-receiver call
    // succeeds and mutates the target.
    function testMappingReceiverOverCodeSucceeds() public {
        ExtcodesizeGuardCaller caller = new ExtcodesizeGuardCaller();
        PokeTarget target = new PokeTarget();
        caller.pokeViaMapping(7, target);
        require(target.pokes() == 1, "mapping-receiver call over code succeeds");
    }
}
