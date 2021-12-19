#pragma once
#include <cstddef>
#include <cstdint>
#include <cassert>
#include <algorithm>
#include <type_traits>
#include <string_view>



namespace mph
{
	namespace detail
	{
		constexpr size_t fnv1a(std::string_view text, size_t seed = 0) noexcept
		{
			size_t r = seed;

			if constexpr (sizeof(size_t) == 4)
				r ^= (size_t)UINT32_C(0x811c9dc5);
			else
				r ^= (size_t)UINT64_C(0xcbf29ce484222325);

			for (char c : text)
			{
				r ^= c;
				if constexpr (sizeof(size_t) == 4)
					r *= (size_t)UINT32_C(0x01000193);
				else
					r *= (size_t)UINT64_C(0x00000100000001B3);
			}

			return r;
		}

		// Chris Wellons bit mixing function.
		constexpr size_t wellons_mix(size_t x) noexcept
		{
#if UINTPTR_MAX == UINT32_MAX
			x ^= x >> 15;
			x *= UINT32_C(0xd168aaad);
			x ^= x >> 15;
			x *= UINT32_C(0xaf723597);
			x ^= x >> 15;
#else
			x ^= x >> 32;
			x *= UINT64_C(0xd6e8feb86659fd93);
			x ^= x >> 32;
			x *= UINT64_C(0xd6e8feb86659fd93);
			x ^= x >> 32;
#endif
			return x;
		}

		constexpr size_t random(size_t seed = 0) noexcept
		{
			return detail::wellons_mix(detail::fnv1a(__DATE__ "$" __TIME__ "$" __FILE__, seed));
		}
	}



	template <typename T>
	struct default_hasher
	{
		constexpr size_t operator()(const T& key) const noexcept
		{
			static_assert(std::is_fundamental_v<T> || std::is_pointer_v<T> || std::is_enum_v<T>);
			return detail::wellons_mix(key);
		}
	};

	template <>
	struct default_hasher<std::string_view>
	{
		constexpr size_t operator()(std::string_view key) const noexcept
		{
			return detail::wellons_mix(detail::fnv1a(key));
		}
	};

	template <typename K>
	struct default_subhasher
	{
		constexpr size_t operator()(const K& key, size_t hash, size_t offset) const noexcept
		{
			if (offset == 0)
				return hash;

			return detail::wellons_mix(hash ^ detail::wellons_mix(offset));
		}
	};



	template <
		size_t Size,
		typename K,
		typename V = void,
		typename Hasher = default_hasher<K>,
		typename Compare = std::equal_to<K>,
		typename Subhash = default_subhasher<K>>
	class hash_dictionary
	{
		static constexpr auto ptr_bits = sizeof(size_t) * 8;
		static_assert(ptr_bits == 32 || ptr_bits == 64);

		static constexpr auto ptr_bits_log2 = ptr_bits == 32 ? 5 : 6;

		template <size_t K>
		using min_uint =
			std::conditional_t<(K > UINT32_MAX), uint64_t,
			std::conditional_t<(K > UINT16_MAX), uint32_t,
			std::conditional_t<(K > UINT8_MAX), uint16_t, uint8_t>>>;

	public:

		using key_type = K;

		using mapped_type = V;

		using value_type = std::conditional_t<std::is_void_v<V>, K, std::pair<K, V>>;

		using size_type = min_uint<Size>;

		using difference_type = std::ptrdiff_t;

		using hasher = Hasher;

		using key_equal = std::equal_to<K>;

		using allocator_type = void;

		using reference = value_type&;
		using const_reference = const reference;

		using pointer = void;
		using const_pointer = const void;

		using iterator = value_type*;
		using const_iterator = value_type* const;

		using local_iterator = void;
		using const_local_iterator = void;

		using node_type = void;

		using insert_result_type = void;

	private:

		static constexpr size_t presence_array_size = Size < ptr_bits ? 1 : ((Size + Size / 2) >> ptr_bits_log2);

		size_t		offsets[Size];
		value_type	entries[Size];

		constexpr auto& entry_at(size_type index) noexcept
		{
			return entries[index];
		}

		constexpr auto& entry_at(size_type index) const noexcept
		{
			return entries[index];
		}

		constexpr auto& offset_at(size_type index) noexcept
		{
			return offsets[index];
		}

		constexpr auto& offset_at(size_type index) const noexcept
		{
			return offsets[index];
		}

		static constexpr bool is_size_pow2 = []
		{
			uint8_t n = 0;
			for (auto k = (size_type)Size; k != 0; k >>= 1)
				if (k & 1)
					++n;
			return n == 1;
		}();

		static constexpr size_type modulo(size_t value) noexcept
		{
			if constexpr (is_size_pow2)
			{
				return (size_type)(value & (Size - 1));
			}
			else
			{
				return value % Size;
			}
		}

		static constexpr auto& get_key(value_type& entry) noexcept
		{
			if constexpr (std::is_void_v<V>)
				return entry;
			else
				return entry.first;
		}

		static constexpr auto& get_key(const value_type& entry) noexcept
		{
			if constexpr (std::is_void_v<V>)
				return entry;
			else
				return entry.first;
		}

		template <typename Collection, typename Extract>
		static constexpr bool generates_collision(
			size_t offset, std::pair<size_t, size_t> bckt,
			const size_t(&next)[Size],
			const size_t(&hashes)[Size],
			size_t(&presence)[presence_array_size],
			Collection&& values,
			Extract&& extract_entry) noexcept
		{
			size_t presence_copy[presence_array_size] = {};
			std::copy(std::begin(presence), std::end(presence), presence_copy);

			for (auto i = bckt.first; i != Size; i = next[i])
			{
				const auto index = modulo(Subhash()(get_key(extract_entry(values, i)), hashes[i], offset));
				if ((presence_copy[index >> ptr_bits_log2] & ((size_t)1 << (index & (ptr_bits - 1)))) != 0)
					return true;
				presence_copy[index >> ptr_bits_log2] |= ((size_t)1 << (index & (ptr_bits - 1)));
			}

			for (size_t i = 0; i != presence_array_size; ++i)
				if (presence[i] != presence_copy[i])
					presence[i] = presence_copy[i];

			return false;
		}

		template <typename Collection, typename Extract>
		constexpr void commit_bucket(
			size_t offset, std::pair<size_t, size_t> bckt,
			const size_t(&next)[Size],
			const size_t(&hashes)[Size],
			Collection&& values,
			Extract&& extract_entry) noexcept
		{
			for (auto i = bckt.first; i != Size; i = next[i])
			{
				offset_at(modulo(hashes[i])) = offset;
				entry_at(modulo(Subhash()(get_key(extract_entry(values, i)), hashes[i], offset))) = std::move(extract_entry(values, i));
			}
		}

		template <typename Collection, typename Extract>
		constexpr void construct_table(Collection&& values, Extract&& extract_entry) noexcept
		{
			using Bucket = std::pair<size_t, size_t>;

			size_t presence[presence_array_size] = {};
			size_t hashes[Size] = {};
			size_t next[Size] = {};
			Bucket buckets[Size] = {};

			size_t min = Size;
			size_t max = 0;
			size_t bucket_count = 0;
			size_t bump = 0;

			std::fill(std::begin(buckets), std::end(buckets), Bucket{ Size, 0 });

			for (size_t i = 0; i != Size; ++i)
			{
				const auto hash = hash_function(get_key(extract_entry(values, i)));
				auto bucket_index = modulo(hash);
				if (!std::is_constant_evaluated())
					assert(bucket_index < Size);
				hashes[i] = hash;
				if (bucket_index > max)
					max = bucket_index;
				if (bucket_index < min)
					min = bucket_index;
				auto& e = buckets[bucket_index];
				if (e.second == 0)
					++bucket_count;
				++e.second;
				next[i] = e.first;
				e.first = i;
			}

			++max;
			std::sort(std::begin(buckets) + min, std::begin(buckets) + max, [](const Bucket& lhs, const Bucket& rhs)
			{
				return lhs.second > rhs.second;
			});

			for (size_t i = min; i < max; ++i)
			{
				size_t offset = 0;
				while (generates_collision(offset, buckets[i], next, hashes, presence, values, extract_entry))
					++offset;
				commit_bucket(offset, buckets[i], next, hashes, values, extract_entry);
			}
		}

	public:

		template <typename T, typename U>
		static constexpr bool key_eq(T&& lhs, U&& rhs) noexcept
		{
			return Compare()(std::forward<T>(lhs), std::forward<U>(rhs));
		}

		template <typename T>
		static constexpr auto hash_function(T&& key) noexcept
		{
			return hasher()(std::forward<T>(key));
		}

		constexpr hash_dictionary() noexcept :
			offsets(), entries()
		{
		}

		template <typename... T>
		constexpr hash_dictionary(T&&... values) noexcept :
			offsets(), entries()
		{
			value_type range[] = { std::forward<T>(values)... };

			construct_table(std::move(range), [](auto& collection, size_t index) constexpr noexcept
			{
				return collection[index];
			});
		}

		template <typename Iterator>
		constexpr hash_dictionary(Iterator&& begin, Iterator&& end) noexcept :
			offsets(), entries()
		{
			auto values = std::make_pair<Iterator, Iterator>(std::forward<Iterator>(begin), std::forward<Iterator>(end));

			construct_table(std::move(values), [](auto& collection, size_t index) constexpr noexcept
			{
				return *std::next(collection.first, index);
			});
		}

		constexpr hash_dictionary(std::initializer_list<value_type>&& values) noexcept :
			offsets(), entries()
		{
			construct_table(values, [](auto& collection, size_t index) constexpr noexcept
			{
				return collection.begin()[index];
			});
		}

		hash_dictionary(const hash_dictionary&) = default;
		hash_dictionary& operator=(const hash_dictionary&) = default;
		~hash_dictionary() = default;

		constexpr auto begin() noexcept { return std::begin(entries); }
		constexpr auto end() noexcept { return std::end(entries); }
		constexpr auto begin() const noexcept { return std::begin(entries); }
		constexpr auto end() const noexcept { return std::end(entries); }
		constexpr auto cbegin() const noexcept { return std::begin(entries); }
		constexpr auto cend() const noexcept { return std::end(entries); }

		static constexpr bool empty() noexcept
		{
			return Size == 0;
		}

		static constexpr size_type size() noexcept
		{
			return (size_type)Size;
		}

		template <typename T>
		constexpr auto find(T&& key) noexcept
		{
			auto k = K(std::forward<T>(key));
			const auto hash = hash_function(k);
			const auto index = modulo(Subhash()(k, hash, offset_at(modulo(hash))));
			auto& e = entry_at(index);
			return key_eq(get_key(e), k) ? &e : end();
		}

		template <typename T>
		constexpr auto find(T&& key) const noexcept
		{
			auto k = K(std::forward<T>(key));
			const auto hash = hash_function(k);
			const auto index = modulo(Subhash()(k, hash, offset_at(modulo(hash))));
			auto& e = entry_at(index);
			return key_eq(get_key(e), k) ? &e : end();
		}

		template <typename T, typename = std::enable_if_t<!std::is_void_v<V>>>
		constexpr auto& at(T&& key) noexcept
		{
			auto it = find(std::forward<T>(key));
			if (!std::is_constant_evaluated())
				assert(it != end());
			return it->second;
		}

		template <typename T, typename = std::enable_if_t<!std::is_void_v<V>>>
		constexpr auto& at(T&& key) const noexcept
		{
			auto it = find(std::forward<T>(key));
			if (!std::is_constant_evaluated())
				assert(it != end());
			return it->second;
		}

		template <typename T, typename = std::enable_if_t<!std::is_same_v<V, void>>>
		constexpr auto& operator[](T&& key) noexcept
		{
			return at(std::forward<T>(key));
		}

		template <typename T, typename = std::enable_if_t<!std::is_same_v<V, void>>>
		constexpr auto& operator[](T&& key) const noexcept
		{
			return at(std::forward<T>(key));
		}

		template <typename T>
		constexpr bool contains(T&& key) const noexcept
		{
			return find(std::forward<T>(key)) != cend();
		}

		template <typename T>
		constexpr size_type count(T&& key) const noexcept
		{
			return (size_type)contains(std::forward<T>(key));
		}

		template <typename T>
		constexpr std::pair<iterator, iterator> equal_range(T&& key) noexcept
		{
			const auto it = find(std::forward<T>(key));
			return std::make_pair(it, it + 1);
		}

		template <typename T>
		constexpr std::pair<const_iterator, const_iterator> equal_range(T&& key) const noexcept
		{
			const auto it = find(std::forward<T>(key));
			return std::make_pair(it, it + 1);
		}

		static constexpr auto bucket_count() noexcept
		{
			return 0;
		}

		static constexpr auto max_bucket_count() noexcept
		{
			return 0;
		}

		template <typename T>
		constexpr auto bucket(T&& key) noexcept
		{
			return (size_type)(find(std::forward<T>(key)) - begin());
		}

		static constexpr float load_factor() noexcept
		{
			return 1.0f;
		}

		static constexpr float max_load_factor() noexcept
		{
			return 1.0f;
		}
	};



	template <
		size_t N,
		typename K,
		typename H = default_hasher<K>,
		typename E = std::equal_to<K>,
		typename S = default_subhasher<K>>
	using hash_set = hash_dictionary<N, K, void, H, E>;

	template <
		size_t N,
		typename K,
		typename V,
		typename H = default_hasher<K>,
		typename E = std::equal_to<K>,
		typename S = default_subhasher<K>,
		typename = std::enable_if_t<!std::is_void_v<V>>>
	using hash_map = hash_dictionary<N, K, V, H, E, S>;



	template <
		size_t N,
		typename K,
		typename H = default_hasher<K>,
		typename E = std::equal_to<K>,
		typename S = default_subhasher<K>>
	constexpr bool operator==(const hash_set<N, K, H, E, S>& lhs, const hash_set<N, K, H, E, S>& rhs) noexcept
	{
		for (auto& e : lhs)
			if (!rhs.contains(e))
				return false;
		return true;
	}
	
	template <
		size_t N,
		typename K,
		typename H = default_hasher<K>,
		typename E = std::equal_to<K>,
		typename S = default_subhasher<K>>
	constexpr bool operator!=(const hash_set<N, K, H, E, S>& lhs, const hash_set<N, K, H, E, S>& rhs) noexcept
	{
		return !(lhs == rhs);
	}
	
	template <
		size_t N,
		typename K,
		typename V,
		typename H = default_hasher<K>,
		typename E = std::equal_to<K>,
		typename S = default_subhasher<K>>
	constexpr bool operator==(const hash_map<N, K, V, H, E, S>& lhs, const hash_map<N, K, V, H, E, S>& rhs) noexcept
	{
		for (auto& e : lhs)
			if (!rhs.contains(e))
				return false;
		return true;
	}
	
	template <
		size_t N,
		typename K,
		typename V,
		typename H = default_hasher<K>,
		typename E = std::equal_to<K>,
		typename S = default_subhasher<K>>
	constexpr bool operator!=(const hash_map<N, K, V, H, E, S>& lhs, const hash_map<N, K, V, H, E, S>& rhs) noexcept
	{
		return !(lhs == rhs);
	}



	template <
		typename K,
		typename H = default_hasher<K>,
		typename E = std::equal_to<K>,
		typename S = default_subhasher<K>,
		typename... U>
	constexpr auto make_set(K&& first, U&&... values) noexcept
	{
		return hash_set<sizeof...(U) + 1, K, H, E, S>(std::move(first), std::forward<U>(values)...);
	}

	template <
		typename K,
		typename V,
		typename H = default_hasher<K>,
		typename E = std::equal_to<K>,
		typename S = default_subhasher<K>,
		typename... U>
	constexpr auto make_map(std::pair<K, V>&& first, U&&... values) noexcept
	{
		return hash_map<sizeof...(U) + 1, K, V, H, E, S>(std::move(first), std::forward<U>(values)...);
	}
}