// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "../src/OpenZeppelinNoncesKeyed.sol";

contract OpenZeppelinNoncesKeyedForgeTest {
    function pack(uint192 key, uint64 nonce) internal pure returns (uint256) {
        return (uint256(key) << 64) | nonce;
    }

    function testKeyZeroReusesBaseNonceStorage() public {
        OpenZeppelinNoncesKeyedHarness harness =
            new OpenZeppelinNoncesKeyedHarness();
        address alice = address(0xA11CE);

        require(harness.nonces(alice) == 0, "base initial");
        require(harness.nonces(alice, 0) == 0, "key zero initial");
        require(harness.useNonce(alice) == 0, "base first");
        require(harness.nonces(alice, 0) == 1, "key zero after base");
        require(harness.useNonceWithKey(alice, 0) == 1, "key zero use");
        require(harness.nonces(alice) == 2, "base after key zero");
    }

    function testNonzeroKeysArePackedAndIndependent() public {
        OpenZeppelinNoncesKeyedHarness harness =
            new OpenZeppelinNoncesKeyedHarness();
        address alice = address(0xA11CE);
        address bob = address(0xB0B);
        uint192 key = 7;
        uint192 otherKey = 8;

        require(harness.nonces(alice, key) == pack(key, 0), "initial keyed");
        require(harness.useNonceWithKey(alice, key) == pack(key, 0), "first");
        require(harness.nonces(alice, key) == pack(key, 1), "after first");
        require(harness.useNonceWithKey(alice, key) == pack(key, 1), "second");
        require(harness.nonces(alice, key) == pack(key, 2), "after second");
        require(harness.nonces(alice, otherKey) == pack(otherKey, 0), "other");
        require(harness.nonces(bob, key) == pack(key, 0), "bob");
    }

    function testCheckedKeyedNonceSuccessAndRollback() public {
        OpenZeppelinNoncesKeyedHarness harness =
            new OpenZeppelinNoncesKeyedHarness();
        address alice = address(0xA11CE);
        uint192 key = 7;

        harness.useCheckedNonceSplit(alice, key, 0);
        require(harness.nonces(alice, key) == pack(key, 1), "checked success");

        try harness.useCheckedNoncePacked(alice, pack(key, 0)) {
            revert("expected invalid nonce");
        } catch (bytes memory data) {
            require(
                keccak256(data) ==
                    keccak256(
                        abi.encodeWithSelector(
                            OpenZeppelinNoncesKeyedBase
                                .InvalidAccountNonce
                                .selector,
                            alice,
                            pack(key, 1)
                        )
                    ),
                "invalid nonce data"
            );
        }

        require(harness.nonces(alice, key) == pack(key, 1), "rollback");
    }

    function testPackUnpackAndUseTwice() public {
        OpenZeppelinNoncesKeyedHarness harness =
            new OpenZeppelinNoncesKeyedHarness();
        address alice = address(0xA11CE);
        uint192 key = 9;
        uint256 packed = pack(key, 42);

        require(harness.packForTest(key, 42) == packed, "pack");

        (uint192 unpackedKey, uint64 unpackedNonce) =
            harness.unpackForTest(packed);
        require(unpackedKey == key, "unpack key");
        require(unpackedNonce == 42, "unpack nonce");

        (uint256 first, uint256 second, uint256 afterNonce) =
            harness.useKeyedTwice(alice, key);
        require(first == pack(key, 0), "first");
        require(second == pack(key, 1), "second");
        require(afterNonce == pack(key, 2), "after");
    }
}
