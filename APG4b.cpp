#include <bits/stdc++.h>
#include <map>
#include <set>
#include <vector>
#include <algorithm>
#include <iostream>
#include <bitset>
#include <cassert>
#include <queue>
#include <stack>
#include <iomanip>
#include <math.h>
#include <time.h>
#include <chrono>
#include <random>
using namespace std;
using namespace chrono;
#define rep(i, n) for (int i = 0; i < (int)n; i++)
#define repf(i, a, b) for (int i = (int)a; i < (int)b; i++)
#define repr(i, a, b) for (int i = (int)a; i > (int)b; i--)
#define all(v) (v).begin(), (v).end()
#define mp(a, b) make_pair(a, b)
#define eb(x) emplace_back(x)
#define F first
#define S second
typedef long long ll;
typedef long double ld;
typedef pair<int, int> pii;
typedef pair<ll, ll> pll;
typedef pair<ld, ld> pdd;
typedef vector<ll> vll;
typedef vector<vll> vvll;
typedef vector<int> vii;
typedef vector<vii> vvii;
const ll mod = 1e9 + 7;
const int infi = 1147483600;
const ll infl = 4e18 + 5;
const char ENDL = '\n';
//cout << fixed << setprecision(17) << res << endl;
const ll MOD = 998244353;

bool debug = true;
int debug_cnt = 0;

const ll T = 10000;
const ll MAX_V = 400;
const ll MIN_V = 200;
const int MAX_Degree = 5;
const ll MAX_DIST = 5000;

inline int string_to_int(string s)
{
    int ans = 0;
    rep(i, s.size())
    {
        ans *= 10;
        ans += (int)((char)s[i] - '0');
    }
    return ans;
}

string int_to_string(int i)
{
    if (i == 0)
        return "00";
    vector<char> moji;
    while (i > 0)
    {
        moji.push_back((char)(i % 10 + (int)'0'));
        i /= 10;
    }
    string ans = "";
    repr(s, moji.size() - 1, -1) ans += moji[s];
    if (ans.size() < 2)
        return "0" + ans;
    return ans;
}

void read_csv(string path, vector<int> &output)
{
    ifstream ifs(path);
    string str_buf;
    string str_conma_buf;
    int idx = 0;
    while (getline(ifs, str_buf))
    {
        istringstream i_stream(str_buf);
        while (getline(i_stream, str_conma_buf, ','))
        {
            output[idx] = (string_to_int(str_conma_buf));
            idx++;
        }
    }
    ifs.close();
}

ld calc_value(int t, vector<ld> hav)
{
    ld cons = T * T - t * t;
    return (hav[0] * 2 * (ld)t - hav[1] + cons * hav[2]);
}

ll CALC_MAIN(string path, ld time_d_rate, ld store_custo_rate, ld stay_rate, ld zero_value_rate)
{

    auto startClock = system_clock::now();
    if (debug)
    {
        cout << "CALC_MAIN start at : "
             << duration_cast<microseconds>(startClock - startClock).count() * 1e-6
             << ENDL;
    }

    ll score = 0;

    //input
    vector<int> input_data(32500);
    if (debug)
    {
        read_csv(path, input_data);
    }
    else
    {
        int idx;
        cin >> input_data[0] >> input_data[1];
        rep(i, input_data[1]) cin >> input_data[3 * i + 2] >> input_data[3 * i + 3] >> input_data[3 * i + 4];
        cin >> input_data[(3 * input_data[1] + 2)];
        idx = 3 * input_data[1] + 3;
        rep(t, T)
        {
            cin >> input_data[idx];
            idx++;
            if (input_data[idx])
            {
                cin >> input_data[idx] >> input_data[idx + 1];
                idx += 2;
            }
        }
    }
    if (debug)
    {
        cout << "input end at : "
             << duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6
             << ENDL;
    }

    //initialize
    int V, E;
    V = input_data[0];
    E = input_data[1];
    vector<multimap<int, int>> edge(V);
    rep(i, E)
    {
        int u, v, d;
        u = input_data[3 * i + 2] - 1;
        v = input_data[3 * i + 3] - 1;
        d = input_data[3 * i + 4];
        edge[u].insert(mp(v, d));
        edge[v].insert(mp(u, d));
    }
    if (debug)
    {
        cout << "init end at : "
             << duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6
             << ENDL;
    }

    //距離の計算
    vector<vector<ld>> dist(V, vector<ld>(V, infi));
    rep(i, V)
    {
        //頂点iからのダイクストラ
        multiset<pair<int, int>> search;
        dist[i][i] = 0;
        search.insert(mp(0, i));
        while (true)
        {
            if (search.empty())
                break;
            int now = (*search.begin()).S;
            search.erase(search.begin());
            for (auto itr = edge[now].begin(); itr != edge[now].end(); itr++)
            {
                int nex = (*itr).F;
                int d = (*itr).S;
                if (dist[i][now] + d < dist[i][nex])
                {
                    dist[i][nex] = dist[i][now] + d;
                    search.insert(mp(dist[i][nex], nex));
                }
            }
        }
    }
    rep(i, V) dist[i][i] = zero_value_rate;
    if (debug)
    {
        cout << "calc dist end at : "
             << duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6
             << ENDL;
    }


//----------------------------------------------------------------------------------------

    //main_treatment
    //注文がk個以上のときすべて回る（0を通ったら追加する）
    //注文がk個未満のとき0へ向かう。（配達完了処理もちゃんとする）
    //注文の優先度：(t-o)^2のコストがかかる。これの小さい順なのでoの大きい順に届ける
    //素直に実装するなら、目的地に到着するまで目的地を変えない。
    //距離行列において、隣接ノードの中で最も目的地との距離が小さいノードを選べばよい？
    //変数の定義など
    
    vector<int> ans(T, -1);
    int idx = 3 * E + 3;
    //main_loop

    if (debug)
    {
        cout << "main init end at : "
             << duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6
             << ENDL;
    }

    rep(t, T)
    {
        //時刻tからt+1の処理をおこなう
        //注文を受け取る
        if (debug && t % 1000 == 0)
        {
            cout << "itr, score : " << t << " " << score << ENDL;
        }
        int ord_num = input_data[idx];
        idx++;
        if (ord_num)
        {
            order_id[t] = input_data[idx];
            idx++;
            int target = input_data[idx] - 1;
            idx++;
            order[target].insert(t);
            //各頂点の評価更新
        }
        //商品を積む

        //行動の決定

        //移動結果の処理
        //配達完了処理とスコアの集計
        //z : 時刻t+1に完了した注文の数
    }
 //----------------------------------------------------------------------------------------

    if (debug)
    {
        cout << "CALC_MAIN end at : "
             << duration_cast<microseconds>(system_clock::now() - startClock).count() * 1e-6
             << ENDL;
    }
    if (!(debug))
    {
        rep(i, T) if (ans[i] != -1) ans[i]++;
        rep(i, T) cout << ans[i] << ENDL;
    }

    return score;
}

int main()
{
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    const string path = "./HH_1/test_A/input_";
    int n = 1;
    string problem = "A";
    rep(i, n)
    {
        ld t_d_rate = 0.01;
        ld s_c_rate = 0.1;
        ld stay_rate = 0;
        ld z_v_rate = 0.0001;
        //t_d_rate：距離のt_d_rate乗分の1の割引を行う。大きいほど近くを重視
        //s_c_rate：顧客に対して店舗を重視する割合。1より大きいと店舗重視
        //1よりちいさい値推奨[0,1]。1より小さいと、受注がある程度貯まるまでは配達を行う
        //stay_rate : 注文価値がこれ未満のときstayする。受注した注文があまりにも少ないとstayする
        string path_in = path + int_to_string(i) + ".csv";
        ld ans = (ld)CALC_MAIN(path_in, t_d_rate, s_c_rate, stay_rate, z_v_rate) / 1000000.0;
        if (debug)
        {
            cout << "final score : " << ans << ENDL;
        }
    }
}