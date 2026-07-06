// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {
    OpenZeppelinAccessControlForwarder,
    OpenZeppelinAccessControlHarness,
    OpenZeppelinIAccessControl,
    OpenZeppelinIERC165
} from "../src/OpenZeppelinAccessControl.sol";

contract OpenZeppelinAccessControlForgeTest {
    function _expectCustom(bytes memory actual, bytes memory expected)
        private
        pure
    {
        require(keccak256(actual) == keccak256(expected), "custom error");
    }

    function testConstructorAdminAndInterfaceIds() public {
        OpenZeppelinAccessControlHarness target =
            new OpenZeppelinAccessControlHarness(address(this));

        require(
            target.DEFAULT_ADMIN_ROLE() == bytes32(uint256(0)),
            "default role"
        );
        require(
            target.hasRole(target.DEFAULT_ADMIN_ROLE(), address(this)),
            "admin"
        );
        require(
            target.getRoleAdmin(target.WRITER_ROLE()) ==
                target.DEFAULT_ADMIN_ROLE(),
            "writer admin"
        );
        require(
            target.supportsInterface(type(OpenZeppelinIAccessControl).interfaceId),
            "access interface"
        );
        require(
            target.supportsInterface(type(OpenZeppelinIERC165).interfaceId),
            "erc165 interface"
        );
        require(!target.supportsInterface(0xffffffff), "unknown interface");
    }

    function testGrantTouchRevokeAndUnauthorizedRollback() public {
        OpenZeppelinAccessControlHarness target =
            new OpenZeppelinAccessControlHarness(address(this));
        OpenZeppelinAccessControlForwarder writer =
            new OpenZeppelinAccessControlForwarder();

        target.grantRole(target.WRITER_ROLE(), address(writer));
        require(target.hasRole(target.WRITER_ROLE(), address(writer)), "granted");
        require(writer.touch(target) == 1, "touch");
        require(target.writes() == 1, "stored write");

        target.revokeRole(target.WRITER_ROLE(), address(writer));
        require(!target.hasRole(target.WRITER_ROLE(), address(writer)), "revoked");

        try writer.touch(target) returns (uint256) {
            revert("expected revert");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinIAccessControl
                        .AccessControlUnauthorizedAccount
                        .selector,
                    address(writer),
                    target.WRITER_ROLE()
                )
            );
        }
        require(target.writes() == 1, "rolled back");
    }

    function testRoleAdminChangeAndDelegatedGrant() public {
        OpenZeppelinAccessControlHarness target =
            new OpenZeppelinAccessControlHarness(address(this));
        OpenZeppelinAccessControlForwarder manager =
            new OpenZeppelinAccessControlForwarder();
        OpenZeppelinAccessControlForwarder writer =
            new OpenZeppelinAccessControlForwarder();

        target.grantRole(target.MANAGER_ROLE(), address(manager));
        target.setWriterAdmin(target.MANAGER_ROLE());
        require(
            target.getRoleAdmin(target.WRITER_ROLE()) == target.MANAGER_ROLE(),
            "new admin"
        );

        try target.grantRole(target.WRITER_ROLE(), address(writer)) {
            revert("expected revert");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinIAccessControl
                        .AccessControlUnauthorizedAccount
                        .selector,
                    address(this),
                    target.MANAGER_ROLE()
                )
            );
        }

        manager.grant(target, target.WRITER_ROLE(), address(writer));
        require(target.hasRole(target.WRITER_ROLE(), address(writer)), "delegated");
        require(writer.touch(target) == 1, "delegated touch");
    }

    function testRenounceConfirmation() public {
        OpenZeppelinAccessControlHarness target =
            new OpenZeppelinAccessControlHarness(address(this));
        OpenZeppelinAccessControlForwarder writer =
            new OpenZeppelinAccessControlForwarder();

        target.grantRole(target.WRITER_ROLE(), address(writer));

        try writer.renounce(target, target.WRITER_ROLE(), address(this)) {
            revert("expected confirmation revert");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinIAccessControl.AccessControlBadConfirmation.selector
                )
            );
        }
        require(target.hasRole(target.WRITER_ROLE(), address(writer)), "kept");

        writer.renounce(target, target.WRITER_ROLE(), address(writer));
        require(!target.hasRole(target.WRITER_ROLE(), address(writer)), "lost");
    }
}
