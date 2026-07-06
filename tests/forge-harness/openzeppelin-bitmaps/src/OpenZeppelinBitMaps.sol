// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Import-free adaptation of OpenZeppelin Contracts v4.9.6
// `utils/structs/BitMaps.sol`.
library OpenZeppelinBitMaps {
    struct BitMap {
        mapping(uint256 => uint256) _data;
    }

    function get(BitMap storage bitmap, uint256 index)
        internal
        view
        returns (bool)
    {
        uint256 bucket = index >> 8;
        uint256 mask = 1 << (index & 0xff);
        return bitmap._data[bucket] & mask != 0;
    }

    function setTo(BitMap storage bitmap, uint256 index, bool value)
        internal
    {
        if (value) {
            set(bitmap, index);
        } else {
            unset(bitmap, index);
        }
    }

    function set(BitMap storage bitmap, uint256 index) internal {
        uint256 bucket = index >> 8;
        uint256 mask = 1 << (index & 0xff);
        bitmap._data[bucket] |= mask;
    }

    function unset(BitMap storage bitmap, uint256 index) internal {
        uint256 bucket = index >> 8;
        uint256 mask = 1 << (index & 0xff);
        bitmap._data[bucket] &= ~mask;
    }
}

contract OpenZeppelinBitMapsHarness {
    using OpenZeppelinBitMaps for OpenZeppelinBitMaps.BitMap;

    OpenZeppelinBitMaps.BitMap private _bitmap;

    event BitMapChanged(uint256 indexed index, bool value);

    function get(uint256 index) external view returns (bool) {
        return _bitmap.get(index);
    }

    function bucket(uint256 bucketIndex) external view returns (uint256) {
        return _bitmap._data[bucketIndex];
    }

    function set(uint256 index) external returns (bool) {
        _bitmap.set(index);
        emit BitMapChanged(index, true);
        return _bitmap.get(index);
    }

    function unset(uint256 index) external returns (bool) {
        _bitmap.unset(index);
        emit BitMapChanged(index, false);
        return _bitmap.get(index);
    }

    function setTo(uint256 index, bool value) external returns (bool) {
        _bitmap.setTo(index, value);
        emit BitMapChanged(index, value);
        return _bitmap.get(index);
    }

    function setPair(uint256 first, uint256 second)
        external
        returns (uint256)
    {
        _bitmap.set(first);
        _bitmap.set(second);
        uint256 bucketIndex = first >> 8;
        return _bitmap._data[bucketIndex];
    }
}
