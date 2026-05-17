//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACK_LLVM_COMPAT_H
#define SMACK_LLVM_COMPAT_H

#include "llvm/Config/llvm-config.h"

#if LLVM_VERSION_MAJOR < 16
#include "llvm/ADT/Optional.h"
#else
#include <optional>
#include <utility>

namespace llvm {
template <typename T> class Optional : public std::optional<T> {
  using Base = std::optional<T>;

public:
  using Base::Base;

  Optional() = default;
  Optional(std::nullopt_t) : Base(std::nullopt) {}
  Optional(const T &V) : Base(V) {}
  Optional(T &&V) : Base(std::move(V)) {}
  Optional(const Base &V) : Base(V) {}
  Optional(Base &&V) : Base(std::move(V)) {}

  bool hasValue() const { return this->has_value(); }
  T &getValue() & { return this->value(); }
  const T &getValue() const & { return this->value(); }
  T &&getValue() && { return std::move(this->value()); }
};

inline constexpr std::nullopt_t None = std::nullopt;
} // namespace llvm
#endif

#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Value.h"

#include <utility>

#if LLVM_VERSION_MAJOR >= 22 && defined(SMACK_ENABLE_SEADSA_LEGACY_LLVM_NAMES)
#define getFixedSize getFixedValue
#define getInt8PtrTy(C) getInt8Ty(C)->getPointerTo()
#define startswith(V) starts_with(V)
#endif

namespace smack {

inline uint64_t fixedTypeSizeInBits(const llvm::DataLayout &DL,
                                    llvm::Type *T) {
  return DL.getTypeSizeInBits(T).getFixedValue();
}

inline uint64_t fixedTypeSizeInBits(const llvm::DataLayout &DL,
                                    const llvm::Type *T) {
  return fixedTypeSizeInBits(DL, const_cast<llvm::Type *>(T));
}

inline uint64_t fixedTypeStoreSizeInBits(const llvm::DataLayout &DL,
                                         llvm::Type *T) {
  return DL.getTypeStoreSizeInBits(T).getFixedValue();
}

inline uint64_t fixedTypeStoreSizeInBits(const llvm::DataLayout &DL,
                                         const llvm::Type *T) {
  return fixedTypeStoreSizeInBits(DL, const_cast<llvm::Type *>(T));
}

inline uint64_t fixedTypeStoreSize(const llvm::DataLayout &DL, llvm::Type *T) {
  return DL.getTypeStoreSize(T).getFixedValue();
}

inline uint64_t fixedTypeStoreSize(const llvm::DataLayout &DL,
                                   const llvm::Type *T) {
  return fixedTypeStoreSize(DL, const_cast<llvm::Type *>(T));
}

inline uint64_t fixedTypeAllocSize(const llvm::DataLayout &DL, llvm::Type *T) {
  return DL.getTypeAllocSize(T).getFixedValue();
}

inline uint64_t fixedTypeAllocSize(const llvm::DataLayout &DL,
                                   const llvm::Type *T) {
  return fixedTypeAllocSize(DL, const_cast<llvm::Type *>(T));
}

// Constructs a pass and hands ownership to llvm::legacy::PassManager via
// PassManager::add(Pass*). The raw `new` is contained here so callsites in
// SmackPipeline.cpp avoid sprinkling allocation noise. Drop this helper once
// the NewPM migration (Phase A5) replaces LegacyPassManager.
template <typename T, typename... Args> inline T *makePass(Args &&...args) {
  return new T(std::forward<Args>(args)...);
}

inline llvm::Type *legacyPointerElementType(const llvm::Value *V) {
#if LLVM_VERSION_MAJOR < 15
#if defined(__clang__)
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wdeprecated-declarations"
#endif
  return V->getType()->getPointerElementType();
#if defined(__clang__)
#pragma clang diagnostic pop
#endif
#else
  (void)V;
  return nullptr;
#endif
}

inline llvm::Type *legacyPointerElementType(const llvm::PointerType *T) {
#if LLVM_VERSION_MAJOR < 15
#if defined(__clang__)
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wdeprecated-declarations"
#endif
  return T->getElementType();
#if defined(__clang__)
#pragma clang diagnostic pop
#endif
#else
  (void)T;
  return nullptr;
#endif
}

} // namespace smack

#endif // SMACK_LLVM_COMPAT_H
