// Copyright 2021 Centrifuge GmbH (centrifuge.io).
// This file is part of Centrifuge chain project.

// Centrifuge is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version (see http://www.gnu.org/licenses).

// Centrifuge is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

//! Crowdloan reward pallet testing environment and utilities
//!
//! The main components implemented in this module is a mock runtime
//! and some helper functions.

use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{
	parameter_types,
	scale_info::TypeInfo,
	sp_runtime::traits::ConvertInto,
	traits::{Contains, InstanceFilter},
};

use sp_consensus_aura::sr25519::AuthorityId as AuraId;
use sp_core::{RuntimeDebug, H256};
use sp_runtime::{
	traits::{BlakeTwo256, IdentityLookup},
	AccountId32, Perbill,
};

use crate as pallet_migration_manager;

pub type AccountId = AccountId32;
pub type Balance = u128;
pub type Index = u32;
pub type BlockNumber = u32;

// Unit = the base number of indivisible units for balances
pub const UNIT: Balance = 1_000_000_000_000;
pub const MILLIUNIT: Balance = 1_000_000_000;
pub const MICROUNIT: Balance = 1_000_000;

// Contracts price units.
pub const MILLICENTS: Balance = 1_000_000_000;
pub const CENTS: Balance = 1_000 * MILLICENTS;
pub const DOLLARS: Balance = 100 * CENTS;

const fn deposit(items: u32, bytes: u32) -> Balance {
	(items as Balance * UNIT + (bytes as Balance) * (5 * MILLIUNIT / 100)) / 10
}

const AVERAGE_ON_INITIALIZE_RATIO: Perbill = Perbill::from_percent(10);
const NORMAL_DISPATCH_RATIO: Perbill = Perbill::from_percent(75);

/// Change this to adjust the block time.
pub const MILLISECS_PER_BLOCK: u64 = 6000;

// NOTE: Currently it is not possible to change the slot duration after the chain has started.
//       Attempting to do so will brick block production.
pub const SLOT_DURATION: u64 = MILLISECS_PER_BLOCK;

/// We allow for 0.5 of a second of compute with a 12 second average block time.
const MAXIMUM_BLOCK_WEIGHT: Weight = WEIGHT_PER_SECOND
	.saturating_div(2)
	.set_proof_size(100u64);

// A few exports that help ease life for downstream crates.
pub use frame_support::{
	construct_runtime,
	dispatch::DispatchClass,
	traits::{ 
		Everything, EqualPrivilegeOnly, Nothing,
		ConstU128, ConstU32, ConstU64, ConstU8, KeyOwnerProofSystem,
		Randomness, StorageInfo,
	},
	weights::{
		constants::{BlockExecutionWeight, ExtrinsicBaseWeight, RocksDbWeight, WEIGHT_PER_SECOND},
		IdentityFee, Weight,
	},
	StorageValue,
};

use frame_system:: {
	limits::{BlockWeights}
};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Runtime>;
type Block = frame_system::mocking::MockBlock<Runtime>;
use pallet_transaction_payment::{ConstFeeMultiplier, CurrencyAdapter, Multiplier};

// Build mock runtime
frame_support::construct_runtime!(
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Event<T>},
		Vesting: pallet_vesting::{Pallet, Call, Storage, Event<T>},
		Proxy: pallet_proxy::{Pallet, Call, Storage, Event<T>},
		Migration: pallet_migration_manager::{Pallet, Call, Storage, Event<T>},

		Timestamp: pallet_timestamp,
		Aura: pallet_aura,

		Contracts: pallet_contracts,
		RandomnessCollectiveFlip: pallet_randomness_collective_flip,
	}
);

parameter_types! {
	// One storage item; value is size 4+4+16+32 bytes = 56 bytes.
	pub const ProxyDepositBase: Balance = 30;
	// Additional storage item size of 32 bytes.
	pub const ProxyDepositFactor: Balance = 5;
	pub const MaxProxies: u16 = 32;
	pub const AnnouncementDepositBase: Balance = 8;
	pub const AnnouncementDepositFactor: Balance = 1;
	pub const MaxPending: u16 = 32;
}

/// The type used to represent the kinds of proxying allowed.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Encode, Decode, RuntimeDebug, TypeInfo)]
pub enum ProxyType {
	Any,
	NonTransfer,
	Governance,
	_Staking,
	NonProxy,
}
impl MaxEncodedLen for ProxyType {
	fn max_encoded_len() -> usize {
		8
	}
}
impl Default for ProxyType {
	fn default() -> Self {
		Self::Any
	}
}
impl InstanceFilter<Call> for ProxyType {
	fn filter(&self, _c: &Call) -> bool {
		true
	}

	fn is_superset(&self, _o: &Self) -> bool {
		false
	}
}

impl sp_consensus_aura::AuraApi<Block, AuraId> for Runtime {
	fn slot_duration() -> sp_consensus_aura::SlotDuration {
		sp_consensus_aura::SlotDuration::from_millis(Aura::slot_duration())
	}

	fn authorities() -> Vec<AuraId> {
		Aura::authorities().into_inner()
	}
}

impl pallet_timestamp::Config for Runtime {
	/// A timestamp: milliseconds since the unix epoch.
	type Moment = u64;
	type OnTimestampSet = Aura;
	type MinimumPeriod = ConstU64<{ SLOT_DURATION / 2 }>;
	type WeightInfo = ();
}

impl pallet_proxy::Config for Runtime {
	type AnnouncementDepositBase = AnnouncementDepositBase;
	type AnnouncementDepositFactor = AnnouncementDepositFactor;
	type RuntimeCall = RuntimeCall;
	type CallHasher = BlakeTwo256;
	type Currency = Balances;
	type RuntimeEvent = RuntimeEvent;
	type MaxPending = MaxPending;
	type MaxProxies = MaxProxies;
	type ProxyDepositBase = ProxyDepositBase;
	type ProxyDepositFactor = ProxyDepositFactor;
	type ProxyType = ProxyType;
	type WeightInfo = pallet_proxy::weights::SubstrateWeight<Self>;
}

// Parameterize balances pallet
parameter_types! {
	pub const MaxLocks: u32 = 10;
	pub const ExistentialDeposit: u64 = 1;
}

// Implement balances pallet configuration for mock runtime
impl pallet_balances::Config for Runtime {
	type AccountStore = System;
	type Balance = Balance;
	type DustRemoval = ();
	type RuntimeEvent = RuntimeEvent;
	type ExistentialDeposit = ExistentialDeposit;
	type MaxLocks = ();
	type MaxReserves = ();
	type ReserveIdentifier = ();
	type WeightInfo = ();
}

// Parameterize vesting pallet
parameter_types! {
	pub const MinVestedTransfer: u64 = 16;
	pub const MaxVestingSchedules: u32 = 4;
}

// Implement vesting pallet configuration for mock runtime
impl pallet_vesting::Config for Runtime {
	type BlockNumberToBalance = ConvertInto;
	type Currency = Balances;
	type RuntimeEvent = RuntimeEvent;
	type MinVestedTransfer = MinVestedTransfer;
	type WeightInfo = ();

	const MAX_VESTING_SCHEDULES: u32 = 1;
}

// Parameterize frame system pallet
parameter_types! {
	pub const BlockHashCount: BlockNumber = 250;
	pub const MaximumBlockWeight: u64 = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::from_percent(75);
}

// Implement frame system pallet configuration for mock runtime
impl frame_system::Config for Runtime {
	type AccountData = pallet_balances::AccountData<Balance>;
	type AccountId = AccountId;
	type BaseCallFilter = BaseFilter;
	type BlockHashCount = BlockHashCount;
	type BlockLength = ();
	type BlockNumber = BlockNumber;
	type BlockWeights = ();
	type RuntimeCall = RuntimeCall;
	type DbWeight = ();
	type RuntimeEvent = RuntimeEvent;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type Header = sp_runtime::generic::Header<BlockNumber, BlakeTwo256>;
	type Index = Index;
	type Lookup = IdentityLookup<Self::AccountId>;
	type MaxConsumers = frame_support::traits::ConstU32<16>;
	type OnKilledAccount = ();
	type OnNewAccount = ();
	type OnSetCode = ();
	type RuntimeOrigin = RuntimeOrigin;
	type PalletInfo = PalletInfo;
	type SS58Prefix = ();
	type SystemWeightInfo = ();
	type Version = ();
}
pub const ACCOUNTS: u32 = 100;
pub const VESTINGS: u32 = 10;
pub const PROXIES: u32 = 10;

parameter_types! {
	pub const MigrationMaxAccounts: u32 = ACCOUNTS;
	pub const MigrationMaxVestings: u32 = VESTINGS;
	pub const MigrationMaxProxies: u32 = PROXIES;
}

// Implement the migration manager pallet
// The actual associated type, which executes the migration can be found in the migration folder
impl pallet_migration_manager::Config for Runtime {
	type RuntimeEvent = RuntimeEvent;
	type MigrationMaxAccounts = MigrationMaxAccounts;
	type WeightInfo = ();
}


parameter_types! {
	pub const DepositPerItem: Balance = deposit(1, 0);
	pub const DepositPerByte: Balance = deposit(0, 1);
	pub const MaxValueSize: u32 = 16 * 1024;
	pub const DeletionQueueDepth: u32 = 128;

	pub RuntimeBlockWeights: BlockWeights = BlockWeights::builder()
		.base_block(BlockExecutionWeight::get())
		.for_class(DispatchClass::all(), |weights| {
			weights.base_extrinsic = ExtrinsicBaseWeight::get();
		})
		.for_class(DispatchClass::Normal, |weights| {
			weights.max_total = Some(NORMAL_DISPATCH_RATIO * MAXIMUM_BLOCK_WEIGHT);
		})
		.for_class(DispatchClass::Operational, |weights| {
			weights.max_total = Some(MAXIMUM_BLOCK_WEIGHT);
			// Operational transactions have some extra reserved space, so that they
			// are included even if block reached `MAXIMUM_BLOCK_WEIGHT`.
			weights.reserved = Some(
				MAXIMUM_BLOCK_WEIGHT - NORMAL_DISPATCH_RATIO * MAXIMUM_BLOCK_WEIGHT
			);
		})
		.avg_block_initialization(AVERAGE_ON_INITIALIZE_RATIO)
		.build_or_panic();
	// The lazy deletion runs inside on_initialize.
	pub DeletionWeightLimit: Weight = RuntimeBlockWeights::get()
		.per_class
		.get(DispatchClass::Normal)
		.max_total
		.unwrap_or(RuntimeBlockWeights::get().max_block);
	pub Schedule: pallet_contracts::Schedule<Runtime> = Default::default();
}

impl pallet_randomness_collective_flip::Config for Runtime {}

impl pallet_aura::Config for Runtime {
	type AuthorityId = AuraId;
	type DisabledValidators = ();
	type MaxAuthorities = ConstU32<32>;
}

parameter_types! {
	pub FeeMultiplier: Multiplier = Multiplier::one();
}

impl pallet_transaction_payment::Config for Runtime {
	type RuntimeEvent = RuntimeEvent;
	type OnChargeTransaction = CurrencyAdapter<Balances, ()>;
	type OperationalFeeMultiplier = ConstU8<5>;
	type WeightToFee = IdentityFee<Balance>;
	type LengthToFee = IdentityFee<Balance>;
	type FeeMultiplierUpdate = ConstFeeMultiplier<FeeMultiplier>;
}

impl pallet_contracts::Config for Runtime {
	type Time = Timestamp;
	type Randomness = RandomnessCollectiveFlip;
	type Currency = Balances;
	type RuntimeEvent = RuntimeEvent;
	type RuntimeCall = RuntimeCall;
	/// The safest default is to allow no calls at all.
	///
	/// Runtimes should whitelist dispatchables that are allowed to be called from contracts
	/// and make sure they are stable. Dispatchables exposed to contracts are not allowed to
	/// change because that would break already deployed contracts. The `Call` structure itself
	/// is not allowed to change the indices of existing pallets, too.
	type CallFilter = Nothing;
	type DepositPerItem = DepositPerItem;
	type DepositPerByte = DepositPerByte;
	type CallStack = [pallet_contracts::Frame<Self>; 31];
	type WeightPrice = pallet_transaction_payment::Pallet<Self>;
	type WeightInfo = pallet_contracts::weights::SubstrateWeight<Self>;
	type ChainExtension = ();
	type DeletionQueueDepth = DeletionQueueDepth;
	type DeletionWeightLimit = DeletionWeightLimit;
	type Schedule = Schedule;
	type AddressGenerator = pallet_contracts::DefaultAddressGenerator;
	type MaxCodeLen = ConstU32<{ 128 * 1024 }>;
	type MaxStorageKeyLen = ConstU32<128>;
}


// our base filter
// allow base system calls needed for block production and runtime upgrade
// other calls will be disallowed
pub struct BaseFilter;

impl Contains<Call> for BaseFilter {
	fn contains(c: &Call) -> bool {
		matches!(
			c,
			// Calls for runtime upgrade
			|Call::System(frame_system::Call::set_code { .. })| Call::System(
				frame_system::Call::set_code_without_checks { .. }
			) // Calls that are present in each block
		)
	}
}

// ----------------------------------------------------------------------------
// Runtime externalities
// ----------------------------------------------------------------------------

// Runtime externalities builder type declaraction.
//
// This type is mainly used for mocking storage in tests. It is the type alias
// for an in-memory, hashmap-based externalities implementation.
pub struct TestExternalitiesBuilder {
	_existential_deposit: u64,
}

// Implement default trait for test externalities builder
impl Default for TestExternalitiesBuilder {
	fn default() -> Self {
		Self {
			_existential_deposit: 1,
		}
	}
}

// Implement test externalities builder
impl TestExternalitiesBuilder {
	pub fn existential_deposit(mut self, existential_deposit: u64) -> Self {
		self._existential_deposit = existential_deposit;
		self
	}

	// Build a genesis storage key/value store
	pub fn build<R>(self, execute: impl FnOnce() -> R) -> sp_io::TestExternalities {
		let mut storage = frame_system::GenesisConfig::default()
			.build_storage::<Runtime>()
			.unwrap();

		pallet_balances::GenesisConfig::<Runtime> {
			balances: vec![(get_account(), 1000)],
		}
		.assimilate_storage(&mut storage)
		.unwrap();

		let mut ext = sp_io::TestExternalities::new(storage);
		ext.execute_with(|| {
			System::set_block_number(1);
		});
		ext.execute_with(execute);
		ext
	}
}

pub(crate) fn get_account() -> AccountId {
	let pub_key: [u8; 32] = [
		89, 211, 18, 12, 18, 109, 171, 175, 21, 236, 203, 33, 33, 168, 153, 55, 198, 227, 184, 139,
		77, 115, 132, 73, 59, 235, 90, 175, 221, 88, 44, 247,
	];

	codec::Decode::decode(&mut &pub_key[..]).unwrap()
}

pub(crate) fn reward_events() -> Vec<pallet_migration_manager::Event<Runtime>> {
	System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| {
			if let Event::Migration(inner) = e {
				Some(inner)
			} else {
				None
			}
		})
		.collect()
}
