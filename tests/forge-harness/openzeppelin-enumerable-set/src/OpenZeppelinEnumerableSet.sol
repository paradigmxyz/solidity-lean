// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Import-inlined, assembly-free adaptation of the UintSet path from
// OpenZeppelin Contracts v4.9.6 `utils/structs/EnumerableSet.sol`.
library OpenZeppelinEnumerableSet {
    struct Set {
        bytes32[] _values;
        mapping(bytes32 => uint256) _indexes;
    }

    function _add(Set storage set, bytes32 value) private returns (bool) {
        if (!_contains(set, value)) {
            set._values.push(value);
            set._indexes[value] = set._values.length;
            return true;
        } else {
            return false;
        }
    }

    function _remove(Set storage set, bytes32 value) private returns (bool) {
        uint256 valueIndex = set._indexes[value];

        if (valueIndex != 0) {
            uint256 toDeleteIndex = valueIndex - 1;
            uint256 lastIndex = set._values.length - 1;

            if (lastIndex != toDeleteIndex) {
                bytes32 lastValue = set._values[lastIndex];
                set._values[toDeleteIndex] = lastValue;
                set._indexes[lastValue] = valueIndex;
            }

            set._values.pop();
            delete set._indexes[value];

            return true;
        } else {
            return false;
        }
    }

    function _contains(Set storage set, bytes32 value)
        private
        view
        returns (bool)
    {
        return set._indexes[value] != 0;
    }

    function _length(Set storage set) private view returns (uint256) {
        return set._values.length;
    }

    function _at(Set storage set, uint256 index)
        private
        view
        returns (bytes32)
    {
        return set._values[index];
    }

    struct UintSet {
        Set _inner;
    }

    function add(UintSet storage set, uint256 value)
        internal
        returns (bool)
    {
        return _add(set._inner, bytes32(value));
    }

    function remove(UintSet storage set, uint256 value)
        internal
        returns (bool)
    {
        return _remove(set._inner, bytes32(value));
    }

    function contains(UintSet storage set, uint256 value)
        internal
        view
        returns (bool)
    {
        return _contains(set._inner, bytes32(value));
    }

    function length(UintSet storage set) internal view returns (uint256) {
        return _length(set._inner);
    }

    function at(UintSet storage set, uint256 index)
        internal
        view
        returns (uint256)
    {
        return uint256(_at(set._inner, index));
    }
}

contract OpenZeppelinEnumerableSetHarness {
    using OpenZeppelinEnumerableSet for OpenZeppelinEnumerableSet.UintSet;

    OpenZeppelinEnumerableSet.UintSet private _set;

    event SetChanged(uint256 indexed value, bool changed);

    function add(uint256 value) external returns (bool) {
        bool changed = _set.add(value);
        emit SetChanged(value, changed);
        return changed;
    }

    function remove(uint256 value) external returns (bool) {
        bool changed = _set.remove(value);
        emit SetChanged(value, changed);
        return changed;
    }

    function contains(uint256 value) external view returns (bool) {
        return _set.contains(value);
    }

    function length() external view returns (uint256) {
        return _set.length();
    }

    function at(uint256 index) external view returns (uint256) {
        return _set.at(index);
    }

    function rawIndex(uint256 value) external view returns (uint256) {
        return _set._inner._indexes[bytes32(value)];
    }

    function addThree(uint256 first, uint256 second, uint256 third)
        external
        returns (uint256)
    {
        _set.add(first);
        _set.add(second);
        _set.add(third);
        return _set.length();
    }
}
