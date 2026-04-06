//Focus on token transfer and approval
// transferFrom()
// approve()
// setApprovalForAll()
// zeroAddressBalanceRevert()

methods{
    function balanceOf(address owner) external returns (uint256) envfree;
    function ownerOf(uint256 tokenId) external returns (address) envfree;
    function unsafeOwnerOf(uint256 tokenId) external returns (address) envfree;
    function unsafeGetApproved(uint256 tokenId) external returns(address) envfree;
    function isApprovedForAll(address owner, address operator) external returns (bool) envfree;
    function _.onERC721Received(address, address, uint256, bytes) external => DISPATCHER(true);
    
    function mint(address to, uint256 tokenId) external;
    function safeMint(address to, uint256 tokenId) external;
    function safeMint(address to, uint256 tokenId, bytes memory data) external;

    function burn(uint256 tokenId) external;

    function transferFrom(address from, address to, uint256 tokenId) external;
    function safeTransferFrom(address from, address to, uint256 tokenId) external;
    function safeTransferFrom(address from, address to, uint256 tokenId, bytes memory data) external;
}

definition nonpayable(env e) returns bool = e.msg.value == 0;
definition nonzerosender(env e) returns bool = e.msg.sender != 0;
definition balanceLimit(address owner) returns bool = balanceOf(owner) < max_uint256;

// ghost for _owner => track how much token owner have
ghost mapping (address => mathint) g_owner{
    init_state axiom forall address a. g_owner[a] == 0; 
}

ghost mathint g_totalSumOwner{
    init_state axiom g_totalSumOwner == 0;
}

hook Sstore _owners[KEY uint256 tokenId] address newOwner(address oldOwner){
    g_owner[newOwner] = g_owner[newOwner] + to_mathint(newOwner != 0 ? 1 : 0);
    g_owner[oldOwner] = g_owner[oldOwner] - to_mathint(oldOwner != 0 ? 1 : 0);
    g_totalSumOwner = g_totalSumOwner + to_mathint(newOwner != 0 ? 1 : 0) - to_mathint(oldOwner != 0 ? 1 : 0);
}

// ghost for balances => track how much balances owner have?
ghost mapping(address => mathint) g_balances{
    init_state axiom forall address a. g_balances[a] == 0;
}

ghost mathint g_supply{
    init_state axiom g_supply == 0;
}

hook Sload uint256 balances _balances[KEY address owner]{
    require g_balances[owner] == to_mathint(balances);
}

hook Sstore _balances[KEY address owner] uint256 newBalance (uint256 oldBalance){
    g_supply = g_supply + newBalance - oldBalance;
}

//TODO: _balance == balanceOf(address) == _owner
invariant balanceOfConsistency(address owner)
    to_mathint(balanceOf(owner)) == g_balances[owner] &&
    to_mathint(balanceOf(owner)) == g_owner[owner];

//TODO: if owner(tokenid) is not 0, then balanceof(owner) > 0
invariant ownerHaveBalances(uint256 tokenId)
    unsafeOwnerOf(tokenId) != 0 => balanceOf(ownerOf(tokenId)) > 0
{
    preserved{
        requireInvariant balanceOfConsistency(ownerOf(tokenId));
    }
}

//TODO: the owned total equals to sum of balances
invariant supplyEqualsToSumBalances()
    g_supply == g_totalSumOwner
{
    preserved mint(address to, uint256 tokenId) with (env e){
        require balanceLimit(to);
    }
    preserved safeMint(address to, uint256 tokenId) with (env e){
        require balanceLimit(to);
    }
    preserved safeMint(address to, uint256 tokenId, bytes data) with (env e){
        require balanceLimit(to);
    }
    preserved burn(uint256 tokenId) with (env e){
        requireInvariant ownerHaveBalances(tokenId);
    }
    preserved transferFrom(address from, address to, uint256 tokenId) with (env e){
        require balanceLimit(to);
        requireInvariant ownerHaveBalances(tokenId);
    }
    preserved safeTransferFrom(address from, address to, uint256 tokenId) with (env e){
        require balanceLimit(to);
        requireInvariant ownerHaveBalances(tokenId);
    }
    preserved safeTransferFrom(address from, address to, uint256 tokenId, bytes data) with (env e){
        require balanceLimit(to);
        requireInvariant ownerHaveBalances(tokenId);
    }
}

//TODO: unminted token (unsafeOwner(tokenId) == 0) => approval(owner(tokenId)) == 0
invariant unmintedTokenNoApproval(uint256 tokenId)
    unsafeOwnerOf(tokenId) == 0 => unsafeGetApproved(tokenId) == 0;

invariant zeroAddressHasNoApprovedOperator (address operator)
    !isApprovedForAll(0, operator)
{
    preserved with (env e){
        require nonzerosender(e);
    }
}

//TODO: assert nft pindah tangan ke owner lain (selain 0), dan hanya bisa dipanggil oleh owner, approved all operator, operator, nft already minted
rule transferFrom(env e, address from, address to, uint256 tokenId){
    //precon
    //check pemilik tokenId berubah
    //check balances nya berubah?
    //check allowance nya berkurang?
    require nonpayable(e);
    require nonzerosender(e);
    requireInvariant ownerHaveBalances(tokenId);
    requireInvariant balanceOfConsistency(from);

    uint256 otherTokenId;
    address otherAccount;
    mathint balanceOtherBefore = balanceOf(otherAccount);
    address ownerOtherBefore = unsafeOwnerOf(otherTokenId);

    mathint balanceFrBefore = balanceOf(from);
    mathint balanceToBefore = balanceOf(to);
    address approvedBefore = unsafeGetApproved(tokenId);
    address ownerBefore = unsafeOwnerOf(tokenId);

    bool isOperator = isApprovedForAll(from, e.msg.sender);

    //action
    transferFrom@withrevert(e, from, to, tokenId);
    bool reverted = lastReverted;

    //post state
    mathint balanceFrAfter = balanceOf(from);
    mathint balanceToAfter = balanceOf(to);
    address approvedAfter = unsafeGetApproved(tokenId);
    address ownerAfter = unsafeOwnerOf(tokenId);

    mathint balanceOtherAfter = balanceOf(otherAccount);
    address ownerOtherAfter = unsafeOwnerOf(otherTokenId);

    //assert liveness
    assert !reverted <=> (
        to != 0 
    );
    
    //sideeffect
    assert (approvedBefore != approvedAfter || isOperator) => (
        balanceFrBefore - 1 == balanceFrAfter &&
        balanceToBefore + 1 == balanceToAfter &&
        ownerBefore != ownerAfter
    );

    assert (ownerBefore != ownerAfter) => (
        balanceFrBefore - 1 == balanceFrAfter &&
        balanceToBefore + 1 == balanceToAfter
    );

    //no side effect
    assert balanceOtherAfter != balanceOtherBefore => otherAccount == from;
    assert ownerOtherAfter != ownerOtherBefore => otherTokenId == tokenId;
}