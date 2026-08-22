#!/usr/bin/env python3
"""Reproduce the finite numerical claims in paper3.tex.

The script uses the defining A/D-cone sums directly and has no third-party
dependencies.  Its bounds follow from H = 2E on each positive-definite cone.
"""

from math import isqrt


MAX_N = 100_000
PRIME_LIMIT = 1_000_001


def h_value(k: int, r: int) -> int:
    return 4 * k * k + 2 * k + r * r + (6 * k + 1) * r


def parity_sign(r: int) -> int:
    return -1 if r % 2 else 1


def cone_data(max_n: int) -> tuple[list[int], list[int]]:
    coeff = [0] * (max_n + 1)
    atom_count = [0] * (max_n + 1)

    # A cone: k,r >= 0.  Here H >= 4k^2 and H >= r^2.
    for k in range(isqrt(max_n // 2) + 3):
        for r in range(isqrt(2 * max_n) + 3):
            e = h_value(k, r) // 2
            if 0 <= e <= max_n:
                coeff[e] -= parity_sign(r)
                atom_count[e] += 1

    # D cone: k=-a, r=-b with a,b >= 1.  Here H >= 2a^2 and
    # b^2-b <= H, so the following integral bounds are safely complete.
    for a in range(1, isqrt(max_n) + 3):
        for b in range(1, isqrt(2 * max_n) + 4):
            e = h_value(-a, -b) // 2
            if 0 <= e <= max_n:
                coeff[e] += parity_sign(-b)
                atom_count[e] += 1

    return coeff, atom_count


def primes_through(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            count = (limit - p * p) // p + 1
            sieve[p * p : limit + 1 : p] = b"\x00" * count
    return [p for p in range(2, limit + 1) if sieve[p]]


def main() -> int:
    coeff, atom_count = cone_data(MAX_N)

    max_abs = max(map(abs, coeff))
    first_max = next(n for n, value in enumerate(coeff) if abs(value) == max_abs)
    norm_zeros = sum(
        1 for n in range(MAX_N + 1) if atom_count[n] > 0 and coeff[n] == 0
    )

    admissible_primes = [
        p for p in primes_through(PRIME_LIMIT) if p % 10 == 1
    ]
    prime_values = [coeff[(p - 1) // 10] for p in admissible_primes]
    prime_abs_1 = sum(abs(value) == 1 for value in prime_values)
    prime_abs_2 = sum(abs(value) == 2 for value in prime_values)
    allowed = {-2, -1, 1, 2}

    pair_count = 0
    multiplicative_pairs = 0
    for i, p in enumerate(admissible_primes):
        for q in admissible_primes[i + 1 :]:
            if p * q > PRIME_LIMIT:
                break
            pair_count += 1
            lhs = coeff[(p * q - 1) // 10]
            rhs = coeff[(p - 1) // 10] * coeff[(q - 1) // 10]
            multiplicative_pairs += lhs == rhs

    expected = {
        "max_abs": 7,
        "first_max": 27_252,
        "norm_zeros": 4_904,
        "admissible_primes": 19_617,
        "prime_abs_1": 13_097,
        "prime_abs_2": 6_520,
        "pair_count": 7_165,
        "multiplicative_pairs": 0,
    }
    actual = {
        "max_abs": max_abs,
        "first_max": first_max,
        "norm_zeros": norm_zeros,
        "admissible_primes": len(admissible_primes),
        "prime_abs_1": prime_abs_1,
        "prime_abs_2": prime_abs_2,
        "pair_count": pair_count,
        "multiplicative_pairs": multiplicative_pairs,
    }
    if set(prime_values) != allowed:
        raise AssertionError(f"prime value set mismatch: {set(prime_values)}")
    if actual != expected:
        raise AssertionError(f"claim mismatch: expected {expected}, got {actual}")

    print("PASS")
    for key, value in actual.items():
        print(f"{key}={value}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
