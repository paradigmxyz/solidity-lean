// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract InheritedEventDuplicateBase {
    event Announced();
}

contract EventDuplicatesInheritedEvent is InheritedEventDuplicateBase {
    event Announced();
}
