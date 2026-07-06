// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {AbiStructTuplesHarnessTarget} from "../src/AbiStructTuples.sol";

contract AbiStructTuplesForgeTest {
    AbiStructTuplesHarnessTarget private target =
        new AbiStructTuplesHarnessTarget();

    function testEncodeDecodeNominalStructWithDynamicField() public {
        bytes memory payload = hex"010203";
        AbiStructTuplesHarnessTarget.Pair memory pair =
            AbiStructTuplesHarnessTarget.Pair({a: 7, b: payload});

        bytes memory encoded = target.encodePair(7, payload);
        require(
            keccak256(encoded) == keccak256(abi.encode(pair)),
            "encode"
        );

        (uint256 a, uint256 length) = target.decodePair(encoded);
        require(a == 7, "decode a");
        require(length == 3, "decode length");
    }

    function testStructAbiRoundTrip() public {
        (uint256 a, uint256 length) = target.roundTrip(11, hex"0506");
        require(a == 11, "round a");
        require(length == 2, "round length");
    }
}
