// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {
    OpenZeppelinAccessControlEnumerableForwarder,
    OpenZeppelinAccessControlEnumerableHarness,
    OpenZeppelinEnumerableIAccessControl,
    OpenZeppelinEnumerableIAccessControlEnumerable,
    OpenZeppelinEnumerableIERC165
} from "../src/OpenZeppelinAccessControlEnumerable.sol";

contract OpenZeppelinAccessControlEnumerableForgeTest {
    function _expectCustom(bytes memory actual, bytes memory expected)
        private
        pure
    {
        require(keccak256(actual) == keccak256(expected), "custom error");
    }

    function testConstructorAdminEnumerationAndInterfaces() public {
        OpenZeppelinAccessControlEnumerableHarness target =
            new OpenZeppelinAccessControlEnumerableHarness(address(this));

        require(
            target.DEFAULT_ADMIN_ROLE() == bytes32(uint256(0)),
            "default role"
        );
        require(
            target.hasRole(target.DEFAULT_ADMIN_ROLE(), address(this)),
            "admin role"
        );
        require(
            target.getRoleMemberCount(target.DEFAULT_ADMIN_ROLE()) == 1,
            "admin count"
        );
        require(
            target.getRoleMember(target.DEFAULT_ADMIN_ROLE(), 0) ==
                address(this),
            "admin member"
        );
        require(
            target.supportsInterface(
                type(OpenZeppelinEnumerableIAccessControlEnumerable).interfaceId
            ),
            "enumerable interface"
        );
        require(
            target.supportsInterface(
                type(OpenZeppelinEnumerableIAccessControl).interfaceId
            ),
            "access interface"
        );
        require(
            target.supportsInterface(type(OpenZeppelinEnumerableIERC165).interfaceId),
            "erc165 interface"
        );
        require(!target.supportsInterface(0xffffffff), "unknown interface");
    }

    function testGrantDuplicateRevokeAndSwapPopEnumeration() public {
        OpenZeppelinAccessControlEnumerableHarness target =
            new OpenZeppelinAccessControlEnumerableHarness(address(this));
        address alice = address(0xa11ce);
        address bob = address(0xb0b);
        address carol = address(0xca801);

        target.grantRole(target.WRITER_ROLE(), alice);
        target.grantRole(target.WRITER_ROLE(), bob);
        target.grantRole(target.WRITER_ROLE(), carol);
        target.grantRole(target.WRITER_ROLE(), bob);

        require(target.getRoleMemberCount(target.WRITER_ROLE()) == 3, "count");
        require(target.getRoleMember(target.WRITER_ROLE(), 0) == alice, "alice");
        require(target.getRoleMember(target.WRITER_ROLE(), 1) == bob, "bob");
        require(target.getRoleMember(target.WRITER_ROLE(), 2) == carol, "carol");

        target.revokeRole(target.WRITER_ROLE(), bob);
        require(!target.hasRole(target.WRITER_ROLE(), bob), "bob revoked");
        require(target.hasRole(target.WRITER_ROLE(), carol), "carol kept");
        require(target.getRoleMemberCount(target.WRITER_ROLE()) == 2, "count 2");
        require(target.getRoleMember(target.WRITER_ROLE(), 1) == carol, "swap");

        try target.getRoleMember(target.WRITER_ROLE(), 2) returns (address) {
            revert("expected bounds revert");
        } catch {}
    }

    function testAdminDelegationRenounceAndRollback() public {
        OpenZeppelinAccessControlEnumerableHarness target =
            new OpenZeppelinAccessControlEnumerableHarness(address(this));
        OpenZeppelinAccessControlEnumerableForwarder manager =
            new OpenZeppelinAccessControlEnumerableForwarder();
        OpenZeppelinAccessControlEnumerableForwarder writer =
            new OpenZeppelinAccessControlEnumerableForwarder();

        target.grantRole(target.MANAGER_ROLE(), address(manager));
        target.setWriterAdmin(target.MANAGER_ROLE());

        try target.grantRole(target.WRITER_ROLE(), address(writer)) {
            revert("expected unauthorized grant");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinEnumerableIAccessControl
                        .AccessControlUnauthorizedAccount
                        .selector,
                    address(this),
                    target.MANAGER_ROLE()
                )
            );
        }
        require(target.getRoleMemberCount(target.WRITER_ROLE()) == 0, "rollback");

        manager.grant(target, target.WRITER_ROLE(), address(writer));
        require(target.hasRole(target.WRITER_ROLE(), address(writer)), "granted");
        require(target.getRoleMemberCount(target.WRITER_ROLE()) == 1, "count");
        require(
            target.getRoleMember(target.WRITER_ROLE(), 0) == address(writer),
            "member"
        );
        require(writer.touch(target) == 1, "touch");

        try writer.renounce(target, target.WRITER_ROLE(), address(this)) {
            revert("expected confirmation revert");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinEnumerableIAccessControl
                        .AccessControlBadConfirmation
                        .selector
                )
            );
        }
        require(target.getRoleMemberCount(target.WRITER_ROLE()) == 1, "kept");

        writer.renounce(target, target.WRITER_ROLE(), address(writer));
        require(!target.hasRole(target.WRITER_ROLE(), address(writer)), "lost");
        require(target.getRoleMemberCount(target.WRITER_ROLE()) == 0, "removed");
    }
}
