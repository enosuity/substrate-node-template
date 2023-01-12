//! # Migration pallet for runtime
//!
//! This pallet provides functionality for migrating a previous chain-state (possibly from a
//! stand-alone chain) to a new chain state (possbily a parachain now). This pallet is necessary due
//! to the exising boundaries that are put onto runtime upgrades from the relay-chain side.
#![cfg_attr(not(feature = "std"), no_std)]
#![allow(clippy::type_complexity)]

use codec::{Decode, Encode};
use frame_support::{dispatch::DispatchResult, ensure, traits::Currency};
pub use pallet::*;
use scale_info::TypeInfo;
pub use weights::*;


#[cfg(test)]
mod mock;
#[cfg(any(test, feature = "runtime-benchmarks"))]
mod test_data;
#[cfg(test)]
mod tests;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
pub mod weights;

#[derive(Encode, Decode, PartialEq, Clone, TypeInfo)]
pub enum MigrationStatus {
	Inactive,
	Ongoing,
	Complete,
}

#[frame_support::pallet]
pub mod pallet {
	use frame_support::{
		pallet_prelude::*,
		sp_runtime::{traits::Saturating, ArithmeticError},
		transactional,
	};
	use frame_system::pallet_prelude::*;
	use log::logger;
use sp_std::vec::Vec;

	// Import various types used to declare pallet in scope.
	use super::*;
	use crate::weights::WeightInfo;

	pub type NumAccounts = u64;

	// Simple declaration of the `Pallet` type. It is placeholder we use to implement traits and
	// method.
	#[pallet::pallet]
	#[pallet::generate_store(pub (super) trait Store)]
	#[pallet::without_storage_info]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config
	+ pallet_balances::Config
	{
		/// Maximum number of accounts that can be migrated at once
		#[pallet::constant]
		type MigrationMaxAccounts: Get<u32>;

		/// Because this pallet emits events, it depends on the runtime's definition of an event.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// WeightInfo
		type WeightInfo: WeightInfo;
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {}

	#[pallet::type_value]
	pub fn OnStatusEmpty() -> MigrationStatus {
		MigrationStatus::Inactive
	}

	#[pallet::storage]
	#[pallet::getter(fn status)]
	pub(super) type Status<T: Config> = StorageValue<_, MigrationStatus, ValueQuery, OnStatusEmpty>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Number of accounts that have been migrated
		MigratedSystemAccounts(u32),
		MigratedBalanceAccounts(u32),
		MigratedContractCodeStorage(u32),

		/// The new and the old issuance after the migration of issuance.
		/// [`OldIssuance`, `NewIssuance`]
		MigratedTotalIssuance(T::Balance, T::Balance),

		/// Indicates that the migration is finished
		MigrationFinished,
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Too many accounts in the vector for the call of `migrate_system_account`.
		TooManyAccounts,
		ZeroBalance,

		/// Indicates that a migration call happened, although the migration is already closed
		MigrationAlreadyCompleted,

		/// Indicates that a finalize call happened, although the migration pallet is not in an
		/// ongoing migration
		OnlyFinalizeOngoing,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Migrating the Account informations from frame_system.
		///
		/// This call takes the raw scale encoded key (= patricia-key for each account in the `Account` storage and inserts
		/// the provided scale encoded value (= `AccountInfo`) into the underlying DB.
		///
		/// Note: As we are converting from substrate-v2 to substrate-v3 we must do type-conversions. Those conversions are done
		/// off-chain.
		/// 
		
		#[pallet::weight(<T as pallet::Config>::WeightInfo::migrate_system_account(T::MigrationMaxAccounts::get()))]
		#[transactional]
		pub fn migrate_contract_code_storage(
			origin: OriginFor<T>,
			code_storages: Vec<(Vec<u8>, Vec<u8>)>,
		) -> DispatchResultWithPostInfo {
			frame_support::log::warn!("=====================Before migrate_contract_code_storage============= Starting ");
			ensure_root(origin)?;

			Self::activate_migration()?;

			frame_support::log::warn!("=====================migrate_contract_code_storage============= Starting ");

			let storage_codes = code_storages.len();
			ensure!(
				code_storages.len()
					<= T::MigrationMaxAccounts::get()
						.try_into()
						.map_err(|_| ArithmeticError::Overflow)?,
				Error::<T>::TooManyAccounts
			);

			for (key, value) in code_storages {
				frame_support::log::warn!("storage::unhashed =======> {:#?}", storage::unhashed::put_raw(key.as_slice(), value.as_slice()));
			}

			// This is safe as MigrationMaxAccounts is a u32
			Self::deposit_event(Event::<T>::MigratedContractCodeStorage(storage_codes as u32));

			Ok(
				Some(<T as pallet::Config>::WeightInfo::migrate_contracts_code_storage(
					storage_codes as u32,
				))
				.into(),
			)
		}

		#[pallet::weight(<T as pallet::Config>::WeightInfo::migrate_system_account(T::MigrationMaxAccounts::get()))]
		#[transactional]
		pub fn migrate_system_account(
			origin: OriginFor<T>,
			accounts: Vec<(Vec<u8>, Vec<u8>)>,
		) -> DispatchResultWithPostInfo {
			
			ensure_root(origin)?;

			Self::activate_migration()?;
			
			let num_accounts = accounts.len();
			
			ensure!(
				accounts.len()
					<= T::MigrationMaxAccounts::get()
						.try_into()
						.map_err(|_| ArithmeticError::Overflow)?,
				Error::<T>::TooManyAccounts
			);

			for (key, value) in accounts {
				frame_support::log::warn!("storage::unhashed =======> {:#?}", storage::unhashed::put_raw(key.as_slice(), value.as_slice()));
				// storage::unhashed::put_raw(key.as_slice(), value.as_slice());
			}

			// This is safe as MigrationMaxAccounts is a u32
			Self::deposit_event(Event::<T>::MigratedSystemAccounts(num_accounts as u32));

			Ok(
				Some(<T as pallet::Config>::WeightInfo::migrate_system_account(
					num_accounts as u32,
				))
				.into(),
			)
		}


		/// Migrates a the `TotalIssuance`.
		///
		/// The provide balance here, will be ADDED to the existing `TotalIssuance` of the system.
		/// Calley better be sure, that the total issuance matches the actual total issuance in the system,
		/// which means, that the `AccountInfo` from the frame_system is migrated afterwards.
		#[pallet::weight(<T as pallet::Config>::WeightInfo::migrate_balances_issuance())]
		#[transactional]
		pub fn migrate_balances_issuance(
			origin: OriginFor<T>,
			additional_issuance: T::Balance,
		) -> DispatchResultWithPostInfo {
			log::warn!(" ============ Starting migrate_balances_issuance ========= ");
			ensure_root(origin)?;

			Self::activate_migration()?;

			let current_issuance = pallet_balances::Pallet::<T>::total_issuance();
			let total_issuance = current_issuance.saturating_add(additional_issuance);
			log::warn!(" ============ Stotal_issuance ========= {:?}", total_issuance);
			let key = <pallet_balances::pallet::TotalIssuance<T> as frame_support::storage::generator::StorageValue<T::Balance>>::storage_value_final_key();
			log::warn!(" ============ key ========= {:?}", key);

			
			// log::warn!(" ============ account_key ========= {:?}", account_key);
			// for (key, value) in vec![(1,2)] {

			// 	let v = <pallet_balances::pallet::Account<T>>::get(key);

			// }
			storage::unhashed::put_raw(&key[..], total_issuance.encode().as_slice());

			Self::deposit_event(Event::<T>::MigratedTotalIssuance(
				current_issuance,
				total_issuance,
			));

			Ok(().into())
		}
		
		/// Update the migration status to `Complete`
		#[pallet::weight(<T as pallet::Config>::WeightInfo::finalize())]
		#[transactional]
		pub fn finalize(origin: OriginFor<T>) -> DispatchResult {
			ensure_root(origin)?;

			ensure!(
				<Status<T>>::get() == MigrationStatus::Ongoing,
				Error::<T>::OnlyFinalizeOngoing
			);

			<Status<T>>::set(MigrationStatus::Complete);

			Self::deposit_event(Event::<T>::MigrationFinished);

			Ok(())
		}
	}
}

impl<T: Config> Pallet<T> {
	fn activate_migration() -> DispatchResult {
		let mut status = <Status<T>>::get();

		if status == MigrationStatus::Inactive {
			<Status<T>>::set(MigrationStatus::Ongoing);
			status = MigrationStatus::Ongoing;
		}

		ensure!(
			status == MigrationStatus::Ongoing,
			Error::<T>::MigrationAlreadyCompleted
		);

		Ok(())
	}
}
