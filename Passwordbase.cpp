#include "iostream"
#include "fstream"
#include "algorithm"
#include "iomanip"
#include "stack"
#include "queue"
#include "string"
#include "vector"
#include "map"
#include "set"
#include "list"
#include "deque"
#include "complex"
#include "bitset"
#include "cmath"
#include "unordered_set"
#include "unordered_map"
#include "iterator"
#include <ctime>
#include <cassert>
#include "numeric"
#include <cstdio>
#include <functional>

using namespace std;

#define f(i, n) for(int i = 0; i < n; i ++)
#define forn(i, j, n) for(int i = j; i < n; i ++)
#define pb push_back
#define maxi(a,b) a = max(a, b);
#define mini(a,b) a = min(a, b);
#define endl '\n'
#define all(a) a.begin(), a.end()
#define rall(a) a.rbegin(), a.rend()
#define sqr(x) ((x) * (x))
#define SZ(a) ((int)(a.size()))
//typedef long long ll;
typedef long double ld;
#define int long long
#define double ld
typedef map<int, int> mii;
typedef pair<int, int> pii;
typedef pair<string, int> psi;
typedef pair<int, string> pis;
typedef vector<int> vi;
typedef vector<double> vd;
typedef vector<pii> vpii;
typedef vector<char> vc;

template<class T>
void show(const vector<T> &a)
{
	for (T x : a)
		cout << x << " ";
	cout << endl;
}

const int sze = 3e5 + 50, oo = 1e18 + 500, mod = 1e9 + 7;
const double eps = 1e-9, PI = 2 * acos(0.0);
vi vertices[sze];
vi visit(sze, 0);
vc used(sze, false);
vi arr(sze, 0);
int n, m, k;
int cnt = 0;

// Serpent cypher functions

bitset<4> S[8][16] = {
	{ 3, 8, 15, 1, 10, 6, 5, 11, 14, 13, 4, 2, 7, 0, 9, 12 },
	{ 15, 12, 2, 7, 9, 0, 5, 10, 1, 11, 14, 8, 6, 13, 3, 4 },
	{ 8, 6, 7, 9, 3, 12, 10, 15, 13, 1, 14, 4, 0, 11, 5, 2 },
	{ 0, 15, 11, 8, 12, 9, 6, 3, 13, 1, 2, 4, 10, 7, 5, 14 },
	{ 1, 15, 8, 3, 12, 0, 11, 6, 2, 5, 4, 10, 9, 14, 7, 13 },
	{ 15, 5, 2, 11, 4, 10, 9, 12, 0, 3, 14, 8, 13, 6, 7, 1 },
	{ 7, 2, 12, 5, 8, 4, 6, 11, 14, 9, 1, 15, 13, 3, 10, 0 },
	{ 1, 13, 15, 0, 14, 8, 2, 11, 7, 4, 12, 10, 9, 3, 5, 6 },
};

bitset<4> S2[8][16] = {
	{ 13, 3, 11, 0,	10,	6,	5,	12,	1,	14,	4,	7,	15,	9,	8,	2 },
	{ 5, 8,	2,	14,	15,	6,	12,	3,	11,	4,	7,	9,	1,	13,	10,	0 },
	{ 12, 9, 15, 4,	11,	14,	1,	2,	0,	3,	6,	13,	5,	8,	10,	7 },
	{ 0, 9,	10,	7,	11,	14,	6,	13,	3,	5,	12,	2,	4,	8,	15,	1 },
	{ 5, 0,	8,	3,	10,	9,	7,	14,	2,	12,	11,	6,	4,	15,	13,	1 },
	{ 8, 15, 2,	9,	4,	1,	13,	14,	11,	6,	5,	3,	7,	12,	10,	0 },
	{ 15, 10, 1, 13, 5,	3,	6,	0,	4,	9,	14,	7,	2,	12,	8,	11 },
	{ 3, 0,	6, 13,	9,	14,	15,	8,	5,	12,	11,	7,	10,	1,	4,	2 },
};

bitset<128> S_direct(bitset<128> X, int j)
{
	bitset<4> x[32];

	f(i, 32)
	{
		forn(j, i * 4, (i + 1) * 4)
		{
			x[i][j % 4] = X[j];
		}
	}

	f(i, 32)
	{
		unsigned k = x[i].to_ulong();
		x[i] = S[j][k];
	}

	f(i, 32)
	{
		forn(j, i * 4, (i + 1) * 4)
		{
			X[j] = x[i][j % 4];
		}
	}

	return X;
}

bitset<128> S_reverse(bitset<128> X, int j)
{
	bitset<4> x[32];

	f(i, 32)
	{
		forn(j, i * 4, (i + 1) * 4)
		{
			x[i][j % 4] = X[j];
		}
	}

	f(i, 32)
	{
		unsigned k = x[i].to_ulong();
		x[i] = S2[j][k];
	}

	f(i, 32)
	{
		forn(j, i * 4, (i + 1) * 4)
		{
			X[j] = x[i][j % 4];
		}
	}

	return X;
}

bitset<32> rol(bitset<32> a, unsigned s)
{
	return (a << s) | (a >> (32 - s));
}

bitset<128> L_direct(bitset<128> X)
{
	bitset<32> x[4];

	f(i, 4)
	{
		forn(j, i * 32, (i + 1) * 32)
		{
			x[i][j % 32] = X[j];
		}
	}

	x[0] = rol(x[0], 13);
	x[2] = rol(x[2], 3);
	x[1] = x[1] ^ x[0] ^ x[2];
	x[3] = x[3] ^ x[2] ^ (x[0] << 3);
	x[1] = rol(x[1], 1);
	x[3] = rol(x[3], 7);
	x[0] = x[0] ^ x[1] ^ x[3];
	x[2] = x[2] ^ x[3] ^ (x[1] << 7);
	x[0] = rol(x[0], 5);
	x[2] = rol(x[2], 22);


	f(i, 4)
	{
		forn(j, i * 32, (i + 1) * 32)
		{
			X[j] = x[i][j % 32];
		}
	}

	return X;
}

bitset<128> L_reverse(bitset<128> X)
{
	bitset<32> x[4];

	f(i, 4)
	{
		forn(j, i * 32, (i + 1) * 32)
		{
			x[i][j % 32] = X[j];
		}
	}

	x[2] = rol(x[2], 10);
	x[0] = rol(x[0], 27);
	x[2] = x[2] ^ x[3] ^ (x[1] << 7);
	x[0] = x[0] ^ x[1] ^ x[3];
	x[3] = rol(x[3], 25);
	x[1] = rol(x[1], 31);
	x[3] = x[3] ^ x[2] ^ (x[0] << 3);
	x[1] = x[1] ^ x[0] ^ x[2];
	x[2] = rol(x[2], 29);
	x[0] = rol(x[0], 19);

	f(i, 4)
	{
		forn(j, i * 32, (i + 1) * 32)
		{
			X[j] = x[i][j % 32];
		}
	}

	return X;
}

bitset<128> IP(bitset<128> x)
{
	bitset<128> temp;

	f(i, 128)
	{
		unsigned j = i / 32;
		temp[4 * (i - 32 * j) + j] = x[i];
	}

	return temp;
}

bitset<128> FP(bitset<128> x)
{
	bitset<128> temp;

	f(i, 128)
	{
		temp[i / 4 + 32 * (i % 4)] = x[i];
	}

	return temp;
}

bitset<128> keys[33];
bitset<32> G = 0x9E3779B9;

void make_keys(bitset<256> key)
{
	bitset<32> W[12];

	f(i, 8)
	{
		forn(j, i * 32, (i + 1) * 32)
		{
			W[i][j % 32] = key[j];
		}
	}

	f(i, 33)
	{
		f(j, 4)
		{
			bitset<32> word = 4 * i + j;
			W[j + 8] = rol(W[j] ^ W[j + 3] ^ W[j + 5] ^ W[j + 7] ^ G ^ word, 11);
		}

		bitset<128> X;
		f(i, 4)
		{
			forn(j, i * 32, (i + 1) * 32)
			{
				X[j] = W[i + 8][j % 32];
			}
		}

		keys[i] = IP(S_direct(X, abs(11 - i) % 8));

		f(i, 7)
		{
			W[i] = W[i + 4];
		}
	}
}

bitset<128> encrypt_serpent(bitset<128> plaintext)
{
	bitset<128> C = IP(plaintext);

	f(i, 31)
	{
		C = L_direct(S_direct(C^keys[i], i % 8));
	}

	C = S_direct(C^keys[31], 7) ^ keys[32];
	C = FP(C);

	return C;
}

bitset<128> decrypt_serpent(bitset<128> ciphertext)
{
	bitset<128> B = IP(ciphertext);

	B = S_reverse(B^keys[32], 7) ^ keys[31];

	for (int i = 30; i >= 0; i--)
	{
		B = S_reverse(L_reverse(B), i % 8) ^ keys[i];
	}

	B = FP(B);

	return B;
}

bitset<256> convert_key(string key)
{
	bitset<256> block;
	bitset<8> blocks[32];

	f(i, 32)
	{
		blocks[i] = (int)key[i];
	}

	f(i, 32)
	{
		for (int j = i * 8; j < (i + 1) * 8; j++)
		{
			block[j] = blocks[i][j % 8];
		}
	}

	return block;
}

bitset<128> convert(string plaintext)
{
	bitset<128> block;
	bitset<8> blocks[16];

	f(i, 16)
	{
		blocks[i] = (int)plaintext[i];
	}

	f(i, 16)
	{
		forn(j, i * 8, (i + 1) * 8)
		{
			block[j] = blocks[i][j % 8];
		}
	}

	return block;
}

string convert(bitset<128> ciphertext)
{
	string plaintext;

	bitset<8> letter;
	f(i, 128)
	{
		letter[i % 8] = ciphertext[i];
		if (i % 8 == 7)
		{
			plaintext.push_back((char)letter.to_ulong());
		}
	}

	return plaintext;
}

string convert(bitset<256> ciphertext)
{
	string plaintext;

	bitset<8> letter;
	f(i, 256)
	{
		letter[i % 8] = ciphertext[i];
		if (i % 8 == 7)
		{
			plaintext.push_back((char)letter.to_ulong());
		}
	}

	return plaintext;
}

bitset<256> encrypt(bitset<256> key, bitset<256> block)
{
	make_keys(key);
	bitset<128> block1;
	bitset<128> block2;
	bitset<256> temp;

	f(i, 128)
	{
		block1[i] = block[i];
	}

	block1 = encrypt_serpent(block1);

	forn(i, 128, 256)
	{
		block2[i % 128] = block[i];
	}

	block2 = encrypt_serpent(block2);


	f(i, 128)
	{
		temp[i] = block1[i];
	}

	forn(i, 128, 256)
	{
		temp[i] = block2[i % 128];
	}

	return temp;
}

bitset<256> hash_function(string plaintext)
{
	bitset<256> hash = 0;

	string str_block;
	bitset<256> key;

	int cnt = 0;

	f(i, plaintext.size())
	{
		str_block.push_back(plaintext[i]);

		if (i % 32 == 31)
		{
			key = convert_key(str_block);
			key = key^hash;
			str_block.clear();
			hash = encrypt(key, hash) ^ hash;
		}
	}

	return hash;
}

string CBCplus_mode_encrypt(string plaintext)
{
	string ciphertext;

	string str_block;
	bitset<128> prev_open_block = 123456789123456789;
	bitset<128> prev_cipher_block = 987654321987654321;
	bitset<128> curr_open_block;
	bitset<128> curr_cipher_block;

	f(i, plaintext.size())
	{
		str_block.push_back(plaintext[i]);

		if (i % 16 == 15)
		{
			curr_open_block = convert(str_block);
			str_block.clear();
			curr_cipher_block = prev_open_block ^ encrypt_serpent(curr_open_block ^ prev_cipher_block);
			ciphertext += convert(curr_cipher_block);
		}
	}

	if (SZ(str_block))
	{
		while (SZ(str_block) != 16)
		{
			str_block += '$';
		}
		curr_open_block = convert(str_block);
		str_block.clear();
		curr_cipher_block = prev_open_block ^ encrypt_serpent(curr_open_block ^ prev_cipher_block);
		ciphertext += convert(curr_cipher_block);
	}

	return ciphertext;
}

string CBCplus_mode_decrypt(string ciphertext)
{
	string plaintext;

	string str_block;
	bitset<128> prev_open_block = 123456789123456789;
	bitset<128> prev_cipher_block = 987654321987654321;
	bitset<128> curr_open_block;
	bitset<128> curr_cipher_block;

	f(i, ciphertext.size())
	{
		str_block.push_back(ciphertext[i]);

		if (i % 16 == 15)
		{
			curr_cipher_block = convert(str_block);
			str_block.clear();
			curr_open_block = prev_cipher_block ^ decrypt_serpent(curr_cipher_block ^ prev_open_block);
			plaintext += convert(curr_open_block);
		}
	}

	return plaintext;
}

string bitset_to_string(bitset<128> block)
{
	string ret;
	for (int i = 0; i < 128; i++)
	{
		ret += block[i] - '0';
	}
	return ret;
}

bitset<128> string_to_bitset(string block)
{
	bitset<128> ret;
	for (int i = 0; i < 128; i++)
	{
		ret[i] = block[i] - '0';
	}
	/*for (int i = 0; i < 128; i++)
	{
		cout << ret[i];
	}*/
	return ret;
}

string encrypting(string plaintext)
{
	string ciphertext;

	string str_block;
	bitset<128> prev_open_block = 123456789123456789;
	bitset<128> prev_cipher_block = 987654321987654321;
	bitset<128> curr_open_block;
	bitset<128> curr_cipher_block;

	f(i, plaintext.size())
	{
		str_block.push_back(plaintext[i]);

		if (i % 16 == 15)
		{
			curr_open_block = convert(str_block);
			str_block.clear();
			curr_cipher_block = prev_open_block ^ encrypt_serpent(curr_open_block ^ prev_cipher_block);
			string temp = curr_cipher_block.to_string();
			reverse(all(temp));
			ciphertext += temp;
		}
	}

	if (SZ(str_block))
	{
		while (SZ(str_block) != 16)
		{
			str_block += '$';
		}
		curr_open_block = convert(str_block);
		str_block.clear();
		curr_cipher_block = prev_open_block ^ encrypt_serpent(curr_open_block ^ prev_cipher_block);
		string temp = curr_cipher_block.to_string();
		reverse(all(temp));
		ciphertext += temp;
	}

	return ciphertext;
}

string decrypting(string ciphertext)
{
	string plaintext;

	string str_block;
	bitset<128> prev_open_block = 123456789123456789;
	bitset<128> prev_cipher_block = 987654321987654321;
	bitset<128> curr_open_block;
	bitset<128> curr_cipher_block;

	f(i, ciphertext.size())
	{
		str_block.push_back(ciphertext[i]);

		if (i % 128 == 127)
		{
			curr_cipher_block = string_to_bitset(str_block);
			str_block.clear();
			curr_open_block = prev_cipher_block ^ decrypt_serpent(curr_cipher_block ^ prev_open_block);
			plaintext += convert(curr_open_block);
		}
	}

	return plaintext;
}

void preparation(string Key)
{
	bitset<256> key = convert_key(Key);
	make_keys(key);
}

// Some useless check functions
void task4()
{
	string Key;
	string plaintext;
	string ciphertext;
	string decyphered;

	cin >> Key >> plaintext;

	bitset<256> key = convert_key(Key);
	make_keys(key);

	string str_block;
	bitset<128> bit_block;

	/*f(i, plaintext.size())
	{
	str_block.push_back(plaintext[i]);

	if (i % 16 == 15)
	{
	bit_block = convert(str_block);
	str_block.clear();
	cout << bit_block << endl;
	cout << convert(bit_block) << endl;
	bit_block = encrypt_serpent(bit_block);
	cout << bit_block << endl;
	cout << convert(bit_block) << endl;
	bit_block = decrypt_serpent(bit_block);
	cout << bit_block << endl;
	cout << convert(bit_block) << endl;
	cout << endl;
	cout << endl;
	}
	}*/

	f(i, plaintext.size())
	{
		str_block.push_back(plaintext[i]);

		if (i % 16 == 15)
		{
			bit_block = convert(str_block);
			str_block.clear();
			bit_block = encrypt_serpent(bit_block);
			ciphertext += convert(bit_block);
			bit_block = decrypt_serpent(bit_block);
			decyphered += convert(bit_block);
		}
	}

	cout << ciphertext << endl << plaintext << endl;
}

void task7()
{
	string plaintext, key;
	cin >> key >> plaintext;
	preparation(key);

	cout << endl << endl << "That is beginning of demonstration of work of enhanced CBC mode using Serpent algorythm." << endl << endl;

	cout << "Plaintext we want to encode: " << endl << endl << "_______" << plaintext << "_______" << endl << endl;
	cout << "Key is: " << key << endl << endl;
	string ciphertext = CBCplus_mode_encrypt(plaintext);

	cout << "Ciphertext we got after encoding: " << endl << endl << "_______" << ciphertext << "_______" << endl << endl;
	cout << "Plaintext we got after decoding: " << endl << endl << "_______" << CBCplus_mode_decrypt(ciphertext) << "_______" << endl << endl;
}

// Password_base version1 here

bool substring(string sub, string str)
{
	m = SZ(sub);
	n = SZ(str);

	for (int i = 0; i < n - m + 1; i++)
	{
		string temp = str.substr(i, m);
		if (temp == sub)
		{
			return true;
		}
	}

	return false;
}

void version1()
{
	string key;
	cout << "Please, print the key to decode or encode passwords" << endl;
	cin >> key;

	string temp;
	while (SZ(temp) < 32)
	{
		temp += key;
	}
	key = temp;
	preparation(key);

	cout << "If you wanna:" << endl;
	cout << "--- add new password, print 'add'" << endl;
	cout << "--- change password, print 'change'" << endl;
	cout << "--- get password, print 'get'" << endl;
	cout << "--- change the key, print 'key'" << endl; 
	string answer;
	cin >> answer;

	vector<pair<string, string>> data;
	ifstream in("base.txt");

	string site, password;
	/*while (getline(in, temp))
	{
		int i = 0;
		site = "";
		password = "";
		while(temp[i] != ' ')
		{
			site += temp[i];
			i++;
		}
		i++;
		while (i < SZ(temp))
		{
			password += temp[i];
			i++;
		}
		data.pb({ site, password });
	}*/
	while (in >> site >> password)
	{
		data.pb({ site, password });
	}
	in.close();

	ofstream out("copy.txt");
	for (auto to : data)
	{
		out << to.first << " " << to.second << endl;
	}
	out.close();

	if (answer == "key")
	{
		cout << "Print new key" << endl;
		cin >> key;

		for (int i = 0; i < SZ(data); i++)
		{
			data[i].second = decrypting(data[i].second);
		}

		string temp;
		while (SZ(temp) < 32)
		{
			temp += key;
		}
		key = temp;
		preparation(key);

		for (int i = 0; i < SZ(data); i++)
		{
			data[i].second = encrypting(data[i].second);
		}

		goto here;
	}

	if (answer == "add" || answer == "change")
	{
		cout << "Ok, print site and password" << endl;
		cin >> site >> password;
		password = encrypting(password);

		if (answer == "change")
		{
			bool fl = false;
			for (int i = 0; i < SZ(data); i ++)
			{
				if (substring(data[i].first, site) || substring(site, data[i].first))
				{
					data[i].second = password;
					fl = true;
					break;
				}
			}

			if (fl)
			{
				cout << "Changes have been saved" << endl;
			}
			else
			{
				cout << "Sorry, no such site has been found" << endl;
			}
		}
		else
		{
			bool fl = false;
			for (auto to : data)
			{
				if (substring(to.first, site) || substring(site, to.first))
				{
					fl = true;
					break;
				}
			}

			if (fl)
			{
				cout << "There is already exists this site here, please, choose option 'change' next time" << endl;
			}
			else
			{
				data.pb({ site, password });
				cout << "New info have been saved" << endl;
			}
		}
	}
	else
	{
		if (answer == "get")
		{
			cout << "Ok, print site to get your password" << endl;
			cin >> site;

			bool fl = false;
			for (auto to : data)
			{
				if (substring(to.first, site) || substring(site, to.first))
				{
					fl = true;
					password = decrypting(to.second);
					cout << "Your password for " << site << " is " << password << endl;
					break;
				}
			}

			if (!fl)
			{
				cout << "Sorry, no such site has been found" << endl;
			}
		}
		else
		{
			cout << "Sorry, you made a mistake in your query, try once again" << endl;
		}
	}

here:
	out.open("base.txt");

	for (auto to : data)
	{
		out << to.first << " " << to.second << endl;
	}

	out.close();
	cout << "Print something or click 'x' to close program" << endl;
	cin >> n;
}

// Password_base version2 here

void backupData(const map<string, string> &data)
{
	ofstream out("copy.txt");
	for (auto &to : data)
	{
		out << to.first << " " << to.second << endl;
	}
	out.close();
}

map<string, string> getData()
{
	map<string, string> data;
	ifstream in("base.txt");

	string site, password;
	while (in >> site >> password)
	{
		data[site] = password;
	}
	in.close();

	return data;
}

void addData(const map<string, string> &data)
{
	ofstream out("base.txt");
	for (auto &to : data)
	{
		out << to.first << " " << to.second << endl;
	}
	out.close();
}

void standardizeKey(string &key)
{
	string temp;
	while (temp.size() < 32)
	{
		temp += key;
	}
	key = temp;
}

void changeKey(map<string, string> &data, string &newKey)
{
	for (auto &info : data)
	{
		info.second = decrypting(info.second);
	}

	standardizeKey(newKey);
	preparation(newKey);

	for (auto &info : data)
	{
		info.second = encrypting(info.second);
	}
}

bool changePassword(map<string, string> &data, const string &site, const string &newPassword)
{
	auto it = data.find(site);

	if (it == data.end())
	{
		return false;
	}

	(*it).second = newPassword;
	return true;
}

bool addPassword(map<string, string> &data, const string &site, const string &password)
{
	auto it = data.find(site);

	if (it == data.end())
	{
		data[site] = password;
		return true;
	}

	return false;
}

bool getPassword(map<string, string> &data, const string &site, string &password)
{
	auto it = data.find(site);

	if (it == data.end())
	{
		return false;
	}

	password = (*it).second;
	return true;
}

bool deletePassword(map<string, string> &data, const string &site)
{
	auto it = data.find(site);

	if (it == data.end())
	{
		return false;
	}

	data.erase(it);
	return true;
}


void findSites(map<string, string> &data, vector<string> &result, char letter)
{
	string key;
	key += letter;

	auto it = data.lower_bound(key);

	while (it != data.end() && (*it).first[0] == letter)
	{
		result.push_back((*it).first);
		it++;
	}
}

void printCommands()
{
	cout << "We store information in format 'site password'" << endl;
	cout << "If you wanna:" << endl;
	cout << "--- find the site name by letter, print 'find'" << endl;
	cout << "--- add new site password, print 'add'" << endl;
	cout << "--- change site password, print 'change'" << endl;
	cout << "--- get site password, print 'get'" << endl;
	cout << "--- delete site password, pring 'delete'" << endl;
	cout << "--- change the key, print 'key'" << endl;
	cout << "--- close the program, print 'x'" << endl;
}

void version2()
{
	cout << "Hello, this is your personal password manager!" << endl;

	cout << endl;
	cout << "************************************ABOUT******************************************" << endl;
	cout << "You should have the key, that will be used for encoding/decoding passwords" << endl;
	cout << "Once you use it for encryption, you need to remember it forever." << endl;
	cout << "Otherwise you will lose access to your passwords, it will be impossible to recover it." << endl;
	cout << "You have the possibility to change the key at every moment. It is a good practice for safety." << endl;
	cout << "If it is the first time you use this manager, come up with a good key --- string of ASCII symbols" << endl;
	cout << "The longer the string --- the better!" << endl;
	cout << "It it is not --- you should remember the last key you used. Do not forget him!" << endl;
	cout << "If you try to use wrong key, you can spoil information forever!" << endl;
	cout << "***********************************************************************************" << endl;
	cout << endl;
	
	string key;
	cout << endl << "Please, print the key to decode or encode passwords" << endl;
	cin >> key;
	standardizeKey(key);
	preparation(key);
	
	printCommands();

	map<string, string> data;

	while (true)
	{
		cout << endl << "What do you wanna do? Print the command from the upper list." << endl;

		data = getData();
		backupData(data);

		string answer;
		cin >> answer;

		if (answer == "key")
		{
			cout << "Print new key" << endl;
			string newKey;
			cin >> newKey;

			changeKey(data, newKey);
			addData(data);
			backupData(data);

			cout << "Key was succesfully changed." << endl;

			continue;
		}

		if (answer == "add" || answer == "change")
		{
			string site, password;
			cout << "Ok, print site:" << endl;
			cin >> site;
			cout << "Print password:" << endl;
			cin >> password;

			password = encrypting(password);

			if (answer == "change")
			{
				bool fl = changePassword(data, site, password);
				
				if (fl)
				{
					addData(data);
					backupData(data);
					cout << "Changes have been saved." << endl;
				}
				else
				{
					cout << "Sorry, this site has not been found, use find to see existing sites." << endl;
				}
			}
			
			if(answer == "add")
			{
				bool fl = addPassword(data, site, password);

				if (fl)
				{
					addData(data);
					backupData(data);
					cout << "New info have been saved." << endl;
				}
				else
				{
					cout << "This site already exists, please, choose option 'change' next time." << endl;
				}
			}

			continue;
		}

		if (answer == "delete")
		{
			cout << "Ok, print site to delete password for:" << endl;
			string site;
			cin >> site;

			bool fl = deletePassword(data, site);

			if (!fl)
			{
				cout << "Sorry, this site has not been found" << endl;
			}
			else
			{
				addData(data);
				backupData(data);
				cout << "Your password for " << site << " was successfully deleted." << endl;
			}

			continue;
		}

		if (answer == "get")
		{
			cout << "Ok, print site to get your password:" << endl;
			string site, password;
			cin >> site;

			bool fl = getPassword(data, site, password);

			if (!fl)
			{
				cout << "Sorry, no such site has been found." << endl;
			}
			else
			{
				password = decrypting(password);
				while (!password.empty() && password.back() == '$')
					password.pop_back();

				cout << "Your password for " << site << " is " << password << endl;
			}

			continue;
		}
			
		if(answer == "find")
		{
			cout << "Ok, print the first letter of the site you are looking for:" << endl;
			char letter;
			cin >> letter;

			vector<string> result;
			findSites(data, result, letter);
			letter = islower(letter) ? toupper(letter) : tolower(letter);
			findSites(data, result, letter);

			cout << "List of sites, starting from yout letter:" << endl;
			for (string &site : result)
			{
				cout << site << endl;
			}

			continue;
		}

		if (answer == "x")
		{
			cout << "See you next time!" << endl;
			break;
		}

		cout << "I do not understand you. Please, choose the command from the list below:" << endl;
		printCommands();
	}
}

signed main()
{
	ios::sync_with_stdio(0);
	cout.tie(0); cin.tie(0);

	version2();

	return 0;
}
