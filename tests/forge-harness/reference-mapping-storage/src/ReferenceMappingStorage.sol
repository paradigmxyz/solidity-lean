// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ReferenceMappingStorage {
    struct Ledger {
        uint256 total;
        mapping(uint256 => uint256) credits;
    }

    struct DynamicBag {
        uint256 total;
        uint256[] numbers;
        bytes raw;
    }

    mapping(uint256 => uint256) private values;
    mapping(uint256 => mapping(uint256 => uint256)) private nested;
    mapping(uint256 => Ledger) private ledgers;
    mapping(uint256 => uint256[]) private lists;
    mapping(uint256 => bytes) private rawValues;
    mapping(uint256 => string) private textValues;
    mapping(uint256 => DynamicBag) private bags;

    function mappingAlias(
        uint256 key,
        uint256 value
    ) external returns (uint256, uint256) {
        mapping(uint256 => uint256) storage local = values;
        local[key] = value;
        return (values[key], local[key]);
    }

    function nestedMappingAlias(
        uint256 outer,
        uint256 key,
        uint256 value
    ) external returns (uint256, uint256) {
        mapping(uint256 => uint256) storage inner = nested[outer];
        inner[key] = value;
        return (nested[outer][key], inner[key]);
    }

    function structMappingAlias(
        uint256 id,
        uint256 key,
        uint256 credit,
        uint256 total
    ) external returns (uint256, uint256, uint256) {
        Ledger storage entry = ledgers[id];
        entry.total = total;
        mapping(uint256 => uint256) storage credits = entry.credits;
        credits[key] = credit;
        return (ledgers[id].total, ledgers[id].credits[key], credits[key]);
    }

    function deleteStructKeepsMapping(
        uint256 id,
        uint256 key,
        uint256 credit,
        uint256 total
    ) external returns (uint256, uint256) {
        ledgers[id].total = total;
        ledgers[id].credits[key] = credit;
        delete ledgers[id];
        return (ledgers[id].total, ledgers[id].credits[key]);
    }

    function structReferenceRebind(
        uint256 firstId,
        uint256 secondId,
        uint256 key,
        uint256 firstCredit,
        uint256 secondCredit,
        uint256 reboundTotal
    ) external returns (uint256, uint256, uint256) {
        Ledger storage selected = ledgers[firstId];
        Ledger storage other = ledgers[secondId];
        selected.credits[key] = firstCredit;
        other.credits[key] = secondCredit;
        selected = other;
        selected.total = reboundTotal;
        selected.credits[key] = secondCredit + 1;
        return (
            ledgers[firstId].credits[key],
            ledgers[secondId].total,
            ledgers[secondId].credits[key]
        );
    }

    function deleteArrayValue(
        uint256 id
    ) external returns (uint256, uint256, uint256, uint256) {
        delete lists[id];
        delete lists[id + 1];

        lists[id].push(11);
        lists[id].push(22);
        lists[id + 1].push(33);

        uint256 beforeLength = lists[id].length;
        uint256 first = lists[id][0];
        delete lists[id];

        return (beforeLength, first, lists[id].length, lists[id + 1].length);
    }

    function deleteBytesValue(
        uint256 id
    ) external returns (uint256, uint256, uint256, uint256) {
        delete rawValues[id];
        delete rawValues[id + 1];

        rawValues[id].push(bytes1(uint8(1)));
        rawValues[id].push(bytes1(uint8(2)));
        rawValues[id + 1].push(bytes1(uint8(3)));

        uint256 beforeLength = rawValues[id].length;
        uint256 second = uint8(rawValues[id][1]);
        delete rawValues[id];

        return (
            beforeLength,
            second,
            rawValues[id].length,
            rawValues[id + 1].length
        );
    }

    function deleteStringValue(
        uint256 id
    ) external returns (string memory, string memory, string memory) {
        textValues[id] = "abc";
        textValues[id + 1] = "z";

        string memory beforeDelete = textValues[id];
        delete textValues[id];

        return (beforeDelete, textValues[id], textValues[id + 1]);
    }

    function deleteStructDynamicValue(
        uint256 id
    )
        external
        returns (
            uint256,
            uint256,
            uint256,
            uint256
        )
    {
        delete bags[id];

        DynamicBag storage bag = bags[id];
        bag.total = 77;
        bag.numbers.push(5);
        bag.numbers.push(6);
        bag.raw.push(bytes1(uint8(0xaa)));

        uint256 beforeDelete =
            bag.total + bag.numbers.length + bag.raw.length;

        delete bags[id];

        return (
            beforeDelete,
            bags[id].total,
            bags[id].numbers.length,
            bags[id].raw.length
        );
    }
}
