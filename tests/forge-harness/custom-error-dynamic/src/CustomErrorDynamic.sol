// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract CustomErrorDynamicHarnessTarget {
    struct Detail {
        uint256 code;
        bytes payload;
    }

    error DynamicBad(string reason, bytes payload);
    error StructBad(Detail detail);

    function failDynamic(string calldata reason, bytes calldata payload)
        external
        pure
    {
        revert DynamicBad(reason, payload);
    }

    function failStruct(uint256 code, bytes calldata payload)
        external
        pure
    {
        revert StructBad(Detail({code: code, payload: payload}));
    }
}
