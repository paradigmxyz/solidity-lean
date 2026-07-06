// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {AbiCoderModesHarnessTarget} from "../src/AbiCoderModes.sol";
import {AbiCoderDirectiveOrder} from "../src/AbiCoderDirectiveOrder.sol";

contract AbiCoderModesForgeTest {
    AbiCoderModesHarnessTarget private target =
        new AbiCoderModesHarnessTarget();
    AbiCoderDirectiveOrder private directiveOrder =
        new AbiCoderDirectiveOrder();

    function testAbiCoderV1DynamicArrayBoundary() public {
        uint256[] memory values = new uint256[](2);
        values[0] = 5;
        values[1] = 7;

        require(target.lengthPlusFirst(values) == 7, "length");
        require(
            keccak256(target.encodeArray(values)) ==
                keccak256(abi.encode(values)),
            "encode"
        );
    }

    function testExplicitV2BeforeLegacyExperimentalPragma() public view {
        require(directiveOrder.ok() == 1, "directive order");
    }
}
