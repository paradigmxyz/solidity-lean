// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/ReferenceDelete.sol";

contract ReferenceDeleteForgeTest {
    function testMemoryReferenceDeleteRebindsLocal() public {
        ReferenceDelete target = new ReferenceDelete();

        uint256[] memory values = new uint256[](2);
        values[0] = 7;
        (uint256 dynamicDeleted, uint256 dynamicAlias) =
            target.dynamicArray(values);
        require(dynamicDeleted == 0, "dynamic deleted");
        require(dynamicAlias == 2, "dynamic alias");

        uint256[2] memory fixedValues;
        fixedValues[0] = 11;
        (uint256 fixedDeleted, uint256 fixedAlias) =
            target.fixedArray(fixedValues);
        require(fixedDeleted == 0, "fixed deleted");
        require(fixedAlias == 11, "fixed alias");

        ReferenceDelete.S memory structInput =
            ReferenceDelete.S({value: 13});
        (uint256 structDeleted, uint256 structAlias) =
            target.structValue(structInput);
        require(structDeleted == 0, "struct deleted");
        require(structAlias == 13, "struct alias");
    }

    function testBytesAndStringDeleteRebindLocals() public {
        ReferenceDelete target = new ReferenceDelete();

        (uint256 bytesDeleted, uint256 bytesAlias) =
            target.bytesValue(hex"0102");
        require(bytesDeleted == 0, "bytes deleted");
        require(bytesAlias == 2, "bytes alias");

        (uint256 stringDeleted, uint256 stringAlias) =
            target.stringValue("abc");
        require(stringDeleted == 0, "string deleted");
        require(stringAlias == 3, "string alias");
    }

    function testNestedDeleteMutatesAliases() public {
        ReferenceDelete target = new ReferenceDelete();

        uint256[] memory elementValues = new uint256[](1);
        elementValues[0] = 17;
        (uint256 elementDeleted, uint256 elementAlias) =
            target.dynamicElement(elementValues);
        require(elementDeleted == 0, "element deleted");
        require(elementAlias == 0, "element alias");

        ReferenceDelete.S memory memberInput =
            ReferenceDelete.S({value: 19});
        (uint256 memberDeleted, uint256 memberAlias) =
            target.structMember(memberInput);
        require(memberDeleted == 0, "member deleted");
        require(memberAlias == 0, "member alias");
    }
}
