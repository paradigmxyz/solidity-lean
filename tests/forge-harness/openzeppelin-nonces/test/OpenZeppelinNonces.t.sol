// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "../src/OpenZeppelinNonces.sol";

contract OpenZeppelinNoncesForgeTest {
    function testUseNonceReturnsCurrentThenIncrements() public {
        OpenZeppelinNoncesHarness harness = new OpenZeppelinNoncesHarness();
        address alice = address(0xA11CE);
        address bob = address(0xB0B);

        require(harness.nonces(alice) == 0, "alice initial");
        require(harness.useNonce(alice) == 0, "alice first");
        require(harness.nonces(alice) == 1, "alice after first");
        require(harness.useNonce(alice) == 1, "alice second");
        require(harness.nonces(alice) == 2, "alice after second");
        require(harness.nonces(bob) == 0, "bob independent");
    }

    function testUseCheckedNonceSuccessAndRollback() public {
        OpenZeppelinNoncesHarness harness = new OpenZeppelinNoncesHarness();
        address alice = address(0xA11CE);

        harness.useCheckedNonce(alice, 0);
        require(harness.nonces(alice) == 1, "checked success");

        try harness.useCheckedNonce(alice, 0) {
            revert("expected invalid nonce");
        } catch (bytes memory data) {
            require(
                keccak256(data) ==
                    keccak256(
                        abi.encodeWithSelector(
                            OpenZeppelinNonces.InvalidAccountNonce.selector,
                            alice,
                            1
                        )
                    ),
                "invalid nonce data"
            );
        }

        require(harness.nonces(alice) == 1, "rollback");
    }

    function testUseTwiceKeepsAccountsIndependent() public {
        OpenZeppelinNoncesHarness harness = new OpenZeppelinNoncesHarness();
        address alice = address(0xA11CE);
        address bob = address(0xB0B);

        harness.useNonce(alice);

        (uint256 first, uint256 second, uint256 afterNonce) =
            harness.useTwice(bob);

        require(first == 0, "first");
        require(second == 1, "second");
        require(afterNonce == 2, "after");
        require(harness.nonces(alice) == 1, "alice");
        require(harness.nonces(bob) == 2, "bob");
    }
}
