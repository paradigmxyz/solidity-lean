// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Import-inlined, assembly-free adaptation of selected paths from
// OpenZeppelin Contracts v4.9.6 `utils/structs/EnumerableMap.sol` and
// `utils/structs/EnumerableSet.sol`. The upstream `keys()` helpers are omitted
// because they use memory-layout assembly, which is outside this source layer.
library OpenZeppelinEnumerableMapSet {
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

    struct Bytes32Set {
        Set _inner;
    }

    function add(Bytes32Set storage set, bytes32 value)
        internal
        returns (bool)
    {
        return _add(set._inner, value);
    }

    function remove(Bytes32Set storage set, bytes32 value)
        internal
        returns (bool)
    {
        return _remove(set._inner, value);
    }

    function contains(Bytes32Set storage set, bytes32 value)
        internal
        view
        returns (bool)
    {
        return _contains(set._inner, value);
    }

    function length(Bytes32Set storage set) internal view returns (uint256) {
        return _length(set._inner);
    }

    function at(Bytes32Set storage set, uint256 index)
        internal
        view
        returns (bytes32)
    {
        return _at(set._inner, index);
    }
}

library OpenZeppelinEnumerableMap {
    using OpenZeppelinEnumerableMapSet for OpenZeppelinEnumerableMapSet.Bytes32Set;

    struct Bytes32ToBytes32Map {
        OpenZeppelinEnumerableMapSet.Bytes32Set _keys;
        mapping(bytes32 => bytes32) _values;
    }

    function set(
        Bytes32ToBytes32Map storage map,
        bytes32 key,
        bytes32 value
    ) internal returns (bool) {
        map._values[key] = value;
        return map._keys.add(key);
    }

    function remove(Bytes32ToBytes32Map storage map, bytes32 key)
        internal
        returns (bool)
    {
        delete map._values[key];
        return map._keys.remove(key);
    }

    function contains(Bytes32ToBytes32Map storage map, bytes32 key)
        internal
        view
        returns (bool)
    {
        return map._keys.contains(key);
    }

    function length(Bytes32ToBytes32Map storage map)
        internal
        view
        returns (uint256)
    {
        return map._keys.length();
    }

    function at(Bytes32ToBytes32Map storage map, uint256 index)
        internal
        view
        returns (bytes32, bytes32)
    {
        bytes32 key = map._keys.at(index);
        return (key, map._values[key]);
    }

    function tryGet(Bytes32ToBytes32Map storage map, bytes32 key)
        internal
        view
        returns (bool, bytes32)
    {
        bytes32 value = map._values[key];
        if (value == bytes32(0)) {
            return (contains(map, key), bytes32(0));
        } else {
            return (true, value);
        }
    }

    function get(Bytes32ToBytes32Map storage map, bytes32 key)
        internal
        view
        returns (bytes32)
    {
        bytes32 value = map._values[key];
        require(
            value != bytes32(0) || contains(map, key),
            "EnumerableMap: nonexistent key"
        );
        return value;
    }

    struct UintToAddressMap {
        Bytes32ToBytes32Map _inner;
    }

    function set(
        UintToAddressMap storage map,
        uint256 key,
        address value
    ) internal returns (bool) {
        return set(
            map._inner,
            bytes32(key),
            bytes32(uint256(uint160(value)))
        );
    }

    function remove(UintToAddressMap storage map, uint256 key)
        internal
        returns (bool)
    {
        return remove(map._inner, bytes32(key));
    }

    function contains(UintToAddressMap storage map, uint256 key)
        internal
        view
        returns (bool)
    {
        return contains(map._inner, bytes32(key));
    }

    function length(UintToAddressMap storage map)
        internal
        view
        returns (uint256)
    {
        return length(map._inner);
    }

    function at(UintToAddressMap storage map, uint256 index)
        internal
        view
        returns (uint256, address)
    {
        (bytes32 key, bytes32 value) = at(map._inner, index);
        return (uint256(key), address(uint160(uint256(value))));
    }

    function tryGet(UintToAddressMap storage map, uint256 key)
        internal
        view
        returns (bool, address)
    {
        (bool success, bytes32 value) = tryGet(map._inner, bytes32(key));
        return (success, address(uint160(uint256(value))));
    }

    function get(UintToAddressMap storage map, uint256 key)
        internal
        view
        returns (address)
    {
        return address(uint160(uint256(get(map._inner, bytes32(key)))));
    }

    struct AddressToUintMap {
        Bytes32ToBytes32Map _inner;
    }

    function set(
        AddressToUintMap storage map,
        address key,
        uint256 value
    ) internal returns (bool) {
        return set(
            map._inner,
            bytes32(uint256(uint160(key))),
            bytes32(value)
        );
    }

    function remove(AddressToUintMap storage map, address key)
        internal
        returns (bool)
    {
        return remove(map._inner, bytes32(uint256(uint160(key))));
    }

    function contains(AddressToUintMap storage map, address key)
        internal
        view
        returns (bool)
    {
        return contains(map._inner, bytes32(uint256(uint160(key))));
    }

    function length(AddressToUintMap storage map)
        internal
        view
        returns (uint256)
    {
        return length(map._inner);
    }

    function at(AddressToUintMap storage map, uint256 index)
        internal
        view
        returns (address, uint256)
    {
        (bytes32 key, bytes32 value) = at(map._inner, index);
        return (address(uint160(uint256(key))), uint256(value));
    }

    function tryGet(AddressToUintMap storage map, address key)
        internal
        view
        returns (bool, uint256)
    {
        (bool success, bytes32 value) =
            tryGet(map._inner, bytes32(uint256(uint160(key))));
        return (success, uint256(value));
    }

    function get(AddressToUintMap storage map, address key)
        internal
        view
        returns (uint256)
    {
        return uint256(get(map._inner, bytes32(uint256(uint160(key)))));
    }
}

contract OpenZeppelinEnumerableMapHarness {
    using OpenZeppelinEnumerableMap for OpenZeppelinEnumerableMap.UintToAddressMap;
    using OpenZeppelinEnumerableMap for OpenZeppelinEnumerableMap.AddressToUintMap;

    OpenZeppelinEnumerableMap.UintToAddressMap private _owners;
    OpenZeppelinEnumerableMap.AddressToUintMap private _balances;

    event OwnerChanged(uint256 indexed tokenId, address indexed owner, bool fresh);
    event BalanceChanged(address indexed account, uint256 balance, bool fresh);

    function setOwner(uint256 tokenId, address owner) external returns (bool) {
        bool fresh = _owners.set(tokenId, owner);
        emit OwnerChanged(tokenId, owner, fresh);
        return fresh;
    }

    function removeOwner(uint256 tokenId) external returns (bool) {
        return _owners.remove(tokenId);
    }

    function ownerContains(uint256 tokenId) external view returns (bool) {
        return _owners.contains(tokenId);
    }

    function ownerLength() external view returns (uint256) {
        return _owners.length();
    }

    function ownerAt(uint256 index) external view returns (uint256, address) {
        return _owners.at(index);
    }

    function ownerTryGet(uint256 tokenId)
        external
        view
        returns (bool, address)
    {
        return _owners.tryGet(tokenId);
    }

    function ownerGet(uint256 tokenId) external view returns (address) {
        return _owners.get(tokenId);
    }

    function setBalance(address account, uint256 balance)
        external
        returns (bool)
    {
        bool fresh = _balances.set(account, balance);
        emit BalanceChanged(account, balance, fresh);
        return fresh;
    }

    function removeBalance(address account) external returns (bool) {
        return _balances.remove(account);
    }

    function balanceContains(address account) external view returns (bool) {
        return _balances.contains(account);
    }

    function balanceLength() external view returns (uint256) {
        return _balances.length();
    }

    function balanceAt(uint256 index) external view returns (address, uint256) {
        return _balances.at(index);
    }

    function balanceTryGet(address account)
        external
        view
        returns (bool, uint256)
    {
        return _balances.tryGet(account);
    }

    function balanceGet(address account) external view returns (uint256) {
        return _balances.get(account);
    }

    function seedThree(address alice, address bob, address carol)
        external
        returns (uint256)
    {
        _owners.set(11, alice);
        _owners.set(22, bob);
        _owners.set(33, carol);
        return _owners.length();
    }
}
