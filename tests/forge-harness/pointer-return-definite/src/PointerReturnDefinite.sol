// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract PointerReturnDefinite {
    uint256[] private first;
    uint256[] private second;

    modifier gate(bool pass) {
        if (pass) {
            _;
        } else {
            revert();
        }
    }

    function chooseStorage(bool pick)
        internal
        view
        returns (uint256[] storage result)
    {
        if (pick) {
            result = first;
        } else {
            result = second;
        }
    }

    function explicitStorage(bool pick)
        internal
        view
        returns (uint256[] storage result)
    {
        if (pick) {
            return first;
        }
        return second;
    }

    function doOnceStorage()
        internal
        view
        returns (uint256[] storage result)
    {
        do {
            result = first;
            break;
        } while (false);
    }

    function modifiedStorage()
        internal
        view
        gate(true)
        returns (uint256[] storage result)
    {
        result = second;
    }

    function chooseCalldata(
        bool pick,
        uint256[] calldata left,
        uint256[] calldata right
    ) internal pure returns (uint256[] calldata result) {
        if (pick) {
            result = left;
        } else {
            result = right;
        }
    }

    function alwaysRevert()
        internal
        pure
        returns (uint256[] calldata result)
    {
        revert();
    }

    function reset() internal {
        delete first;
        delete second;
        first.push(11);
        second.push(22);
    }

    function runStorage(bool pick) external returns (uint256) {
        reset();
        uint256[] storage result = chooseStorage(pick);
        return result[0];
    }

    function runExplicit(bool pick) external returns (uint256) {
        reset();
        uint256[] storage result = explicitStorage(pick);
        return result[0];
    }

    function runDoOnce() external returns (uint256) {
        reset();
        uint256[] storage result = doOnceStorage();
        return result[0];
    }

    function runModified() external returns (uint256) {
        reset();
        uint256[] storage result = modifiedStorage();
        return result[0];
    }

    function runCalldata(
        bool pick,
        uint256[] calldata left,
        uint256[] calldata right
    ) external pure returns (uint256) {
        uint256[] calldata result = chooseCalldata(pick, left, right);
        return result[0];
    }
}
