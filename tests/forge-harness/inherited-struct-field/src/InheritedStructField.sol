// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

/// #197 INHERITED-STRUCT-FIELD-ACCESS: field access on BASE-declared storage
/// structs from a derived contract (direct var, mapping element, array
/// element, compound write, grandparent-declared var).
contract StructBase {
    struct P {
        uint256 a;
        uint256 b;
    }
    struct Item {
        uint256 amount;
        uint256 ts;
    }
    P internal p;
    mapping(uint256 => Item) internal _items;
    P[] internal arr;
}

contract StructMid is StructBase {}

contract InheritedStructFieldTarget is StructMid {
    // Grandparent-declared struct var: field write + read.
    function setA(uint256 v) public {
        p.a = v;
    }

    function getA() public view returns (uint256) {
        return p.a;
    }

    // Inherited mapping(=>struct) element: field write, compound write, read.
    function addItem(uint256 k, uint256 v) public {
        _items[k].amount = v;
    }

    function bumpItem(uint256 k) public {
        _items[k].amount += 1;
    }

    function itemAmount(uint256 k) public view returns (uint256) {
        return _items[k].amount;
    }

    // Inherited struct[] element: push + element field read.
    function pushArr(uint256 v) public {
        arr.push(P(v, v + 1));
    }

    function firstA() public view returns (uint256) {
        return arr[0].a;
    }

    // Control: whole-struct memory copy of an inherited storage struct.
    function getViaCopy() public view returns (uint256) {
        P memory q = p;
        return q.a;
    }
}

/// Control: the BASE reading its own field is unaffected.
contract StructBaseSelf {
    struct P {
        uint256 a;
        uint256 b;
    }
    P internal p;

    function setA(uint256 v) public {
        p.a = v;
    }

    function getA() public view returns (uint256) {
        return p.a;
    }
}

/// Control: struct TYPE from the base, state var declared in the derived.
contract StructTypeFromBase is StructBase {
    P internal own;

    function setOwn(uint256 v) public {
        own.a = v;
    }

    function getOwn() public view returns (uint256) {
        return own.a;
    }
}
