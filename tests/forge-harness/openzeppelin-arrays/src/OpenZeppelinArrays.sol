// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

// Import-inlined, assembly-free adaptation of selected functions from
// OpenZeppelin Contracts v5.6.1 `utils/Arrays.sol` and `utils/math/Math.sol`.
library OpenZeppelinArraysMath {
    function average(uint256 a, uint256 b) internal pure returns (uint256) {
        unchecked {
            return (a & b) + (a ^ b) / 2;
        }
    }
}

library OpenZeppelinArrays {
    function findUpperBound(uint256[] storage array, uint256 element)
        internal
        view
        returns (uint256)
    {
        uint256 low = 0;
        uint256 high = array.length;

        if (high == 0) {
            return 0;
        }

        while (low < high) {
            uint256 mid = OpenZeppelinArraysMath.average(low, high);

            if (array[mid] > element) {
                high = mid;
            } else {
                low = mid + 1;
            }
        }

        if (low > 0 && array[low - 1] == element) {
            return low - 1;
        } else {
            return low;
        }
    }

    function lowerBound(uint256[] storage array, uint256 element)
        internal
        view
        returns (uint256)
    {
        uint256 low = 0;
        uint256 high = array.length;

        if (high == 0) {
            return 0;
        }

        while (low < high) {
            uint256 mid = OpenZeppelinArraysMath.average(low, high);

            if (array[mid] < element) {
                unchecked {
                    low = mid + 1;
                }
            } else {
                high = mid;
            }
        }

        return low;
    }

    function upperBound(uint256[] storage array, uint256 element)
        internal
        view
        returns (uint256)
    {
        uint256 low = 0;
        uint256 high = array.length;

        if (high == 0) {
            return 0;
        }

        while (low < high) {
            uint256 mid = OpenZeppelinArraysMath.average(low, high);

            if (array[mid] > element) {
                high = mid;
            } else {
                unchecked {
                    low = mid + 1;
                }
            }
        }

        return low;
    }

    function lowerBoundMemory(uint256[] memory array, uint256 element)
        internal
        pure
        returns (uint256)
    {
        uint256 low = 0;
        uint256 high = array.length;

        if (high == 0) {
            return 0;
        }

        while (low < high) {
            uint256 mid = OpenZeppelinArraysMath.average(low, high);

            if (array[mid] < element) {
                unchecked {
                    low = mid + 1;
                }
            } else {
                high = mid;
            }
        }

        return low;
    }

    function upperBoundMemory(uint256[] memory array, uint256 element)
        internal
        pure
        returns (uint256)
    {
        uint256 low = 0;
        uint256 high = array.length;

        if (high == 0) {
            return 0;
        }

        while (low < high) {
            uint256 mid = OpenZeppelinArraysMath.average(low, high);

            if (array[mid] > element) {
                high = mid;
            } else {
                unchecked {
                    low = mid + 1;
                }
            }
        }

        return low;
    }
}

contract OpenZeppelinArraysHarness {
    using OpenZeppelinArrays for uint256[];

    uint256[] private _values;

    function seedSorted() external returns (uint256) {
        _values.push(1);
        _values.push(3);
        _values.push(3);
        _values.push(7);
        return _values.length;
    }

    function length() external view returns (uint256) {
        return _values.length;
    }

    function at(uint256 index) external view returns (uint256) {
        return _values[index];
    }

    function lowerStorage(uint256 element) external view returns (uint256) {
        return _values.lowerBound(element);
    }

    function upperStorage(uint256 element) external view returns (uint256) {
        return _values.upperBound(element);
    }

    function findUpperStorage(uint256 element) external view returns (uint256) {
        return _values.findUpperBound(element);
    }

    function lowerMemory(uint256[] memory array, uint256 element)
        external
        pure
        returns (uint256)
    {
        return OpenZeppelinArrays.lowerBoundMemory(array, element);
    }

    function upperMemory(uint256[] memory array, uint256 element)
        external
        pure
        returns (uint256)
    {
        return OpenZeppelinArrays.upperBoundMemory(array, element);
    }

    function average(uint256 a, uint256 b) external pure returns (uint256) {
        return OpenZeppelinArraysMath.average(a, b);
    }
}
