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

rule mint(env e, address owner, uint256 tokenId){
    //precon
    require nonpayable(e);
    require balanceLimit(owner);

    address otherOwner;
    uint256 otherTokenId;

    mathint balanceOwnerBefore = balanceOf(owner);
    address ownerTokenIdBefore = ownerOf(tokenId);
    mathint balanceOtherOwnerBefore = balanceOf(otherOwner);
    address ownerOtherTokenIdBefore = ownerOf(otherTokenId);

    require otherTokenId != tokenId;
    require otherOwner != owner;

    //action
    mint@withrevert(e, owner, tokenId);
    bool reverted = lastReverted;

    //poststate
    mathint balanceOwnerAfter = balanceOf(owner);
    address ownerTokenIdAfter = ownerOf(tokenId);
    mathint balanceOtherOwnerAfter = balanceOf(otherOwner);
    address ownerOtherTokenIdAfter = ownerOf(otherTokenId);

    //liveness
    assert !reverted <=> (
        ownerTokenIdBefore == 0 &&
        owner != 0
    );

    //side effect
    assert !reverted => (
        balanceOwnerAfter == balanceOwnerBefore + 1 &&
        ownerTokenIdAfter == owner
    );

    //no side effect
    assert balanceOtherOwnerBefore == balanceOtherOwnerAfter && ownerOtherTokenIdBefore == ownerOtherTokenIdAfter;
}


//TODO: verify burn success -> balance -, owner == burner
rule burn(env e, uint256 tokenId){
    //precon
    require nonpayable(e);

    address from = unsafeOwnerOf(tokenId);
    uint256 otherTokenId;
    address otherAccount;
    // address otherOwner;


    // uint256 balanceOwnerTokenIdBefore = balanceOf(from);
    // uint256 balanceOtherOwnerBefore = balanceOf(otherOwner);
    // address ownerTokenIdBefore = unsafeOwnerOf(tokenId);
    // address ownerOtherTokenIdBefore = unsafeOwnerOf(otherTokenId);

    uint256 balanceOfFromBefore  = balanceOf(from);
    uint256 balanceOfOtherBefore = balanceOf(otherAccount);
    address ownerBefore          = unsafeOwnerOf(tokenId);
    address otherOwnerBefore     = unsafeOwnerOf(otherTokenId);

    // require otherTokenId != tokenId;
    // require ownerOtherTokenIdBefore != ownerTokenIdBefore;

    //action
    burn@withrevert(e, tokenId);
    // bool reverted = lastReverted;
    bool success = !lastReverted;

    //poststate
    // address ownerTokenIdAfter = unsafeOwnerOf(tokenId);
    // mathint balanceOwnerTokenIdAfter = balanceOf(ownerTokenIdBefore);
    // address ownerOtherTokenIdAfter = unsafeOwnerOf(otherTokenId);
    // mathint balanceOtherOwnerAfter = balanceOf(ownerOtherTokenIdBefore);

    //assert Liveness
    assert success <=> (
        ownerBefore != 0
    );

    //side effect
    assert success => (
        // to_mathint(balanceOf(ownerTokenIdBefore)) == balanceOwnerTokenIdBefore - 1 &&
        // unsafeOwnerOf(tokenId)      == 0 
        to_mathint(balanceOf(from)) == balanceOfFromBefore - 1 &&
        unsafeOwnerOf(tokenId)      == 0
    );

    //no side effect
    // assert balanceOf(otherOwner)           != balanceOtherOwnerBefore => otherOwner == from;
    // assert unsafeOwnerOf(otherTokenId)     != ownerOtherTokenIdBefore => otherTokenId == tokenId;
    assert balanceOf(otherAccount)         != balanceOfOtherBefore => otherAccount == from;
    assert unsafeOwnerOf(otherTokenId)     != otherOwnerBefore     => otherTokenId == tokenId;
}


rule burn_example(env e, uint256 tokenId) {
    require nonpayable(e);

    address from = unsafeOwnerOf(tokenId);
    uint256 otherTokenId;
    address otherAccount;

    // requireInvariant ownerHasBalance(tokenId);

    // mathint supplyBefore         = _supply;
    uint256 balanceOfFromBefore  = balanceOf(from);
    uint256 balanceOfOtherBefore = balanceOf(otherAccount);
    address ownerBefore          = unsafeOwnerOf(tokenId);
    address otherOwnerBefore     = unsafeOwnerOf(otherTokenId);
    address otherApprovalBefore  = unsafeGetApproved(otherTokenId);

    burn@withrevert(e, tokenId);
    bool success = !lastReverted;

    // liveness
    assert success <=> (
        ownerBefore != 0
    );

    // effect
    assert success => (
        // unsafeOwnerOf(tokenId)      != 0 => (_supply == supplyBefore - 1) && // modified for the Prover v8.3.1
        to_mathint(balanceOf(from)) == balanceOfFromBefore - 1 &&
        unsafeOwnerOf(tokenId)      == 0 &&
        unsafeGetApproved(tokenId)  == 0
    );

    // no side effect
    assert balanceOf(otherAccount)         != balanceOfOtherBefore => otherAccount == from;
    assert unsafeOwnerOf(otherTokenId)     != otherOwnerBefore     => otherTokenId == tokenId;
    assert unsafeGetApproved(otherTokenId) != otherApprovalBefore  => otherTokenId == tokenId;
}