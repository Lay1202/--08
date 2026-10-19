#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include <time.h>

#define V          50
#define SPARSE_E   100
#define DENSE_E    600
#define MAX_W      100

static int g_print_edges = 0;

typedef struct {
    int u, v, w;
} Edge;

typedef struct AdjNode {
    int to;
    int w;
    struct AdjNode *next;
} AdjNode;

typedef struct {
    AdjNode *head[V];
    AdjNode *pool;
    int      used;
    int      edgeCount;
} AdjList;

typedef struct {
    int matrix[V][V];
    int edgeCount;
} AdjMatrix;

static int uf_find(int *p, int x) {
    while (p[x] != x) {
        p[x] = p[p[x]];
        x = p[x];
    }
    return x;
}

static int is_connected(const Edge *edges, int m) {
    int parent[V], comps = V;
    for (int i = 0; i < V; i++) parent[i] = i;
    for (int i = 0; i < m; i++) {
        int a = uf_find(parent, edges[i].u);
        int b = uf_find(parent, edges[i].v);
        if (a != b) {
            parent[a] = b;
            comps--;
        }
    }
    return comps == 1;
}

static void generate_graph(Edge *edges, int m) {
    static char exist[V][V];

    do {
        memset(exist, 0, sizeof(exist));
        int perm[V], cnt = 0;

        for (int i = 0; i < V; i++) perm[i] = i;
        for (int i = V - 1; i > 0; i--) {
            int j = rand() % (i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }

        for (int i = 1; i < V; i++) {
            int u = perm[i];
            int v = perm[rand() % i];
            exist[u][v] = exist[v][u] = 1;
            edges[cnt].u = u;
            edges[cnt].v = v;
            edges[cnt].w = rand() % MAX_W + 1;
            cnt++;
        }

        while (cnt < m) {
            int u = rand() % V;
            int v = rand() % V;
            if (u == v || exist[u][v]) continue;
            exist[u][v] = exist[v][u] = 1;
            edges[cnt].u = u;
            edges[cnt].v = v;
            edges[cnt].w = rand() % MAX_W + 1;
            cnt++;
        }
    } while (!is_connected(edges, m));
}

static void build_adj_list(AdjList *g, const Edge *edges, int m) {
    memset(g->head, 0, sizeof(g->head));
    g->pool = (AdjNode *)malloc(sizeof(AdjNode) * 2 * m);
    if (!g->pool) { fprintf(stderr, "malloc failed\n"); exit(1); }
    g->used = 0;
    g->edgeCount = m;

    for (int i = 0; i < m; i++) {
        int u = edges[i].u, v = edges[i].v, w = edges[i].w;

        AdjNode *a = &g->pool[g->used++];
        a->to = v; a->w = w; a->next = g->head[u]; g->head[u] = a;

        AdjNode *b = &g->pool[g->used++];
        b->to = u; b->w = w; b->next = g->head[v]; g->head[v] = b;
    }
}

static void build_adj_matrix(AdjMatrix *g, const Edge *edges, int m) {
    memset(g->matrix, 0, sizeof(g->matrix));
    g->edgeCount = m;
    for (int i = 0; i < m; i++) {
        g->matrix[edges[i].u][edges[i].v] = edges[i].w;
        g->matrix[edges[i].v][edges[i].u] = edges[i].w;
    }
}

static void sift_down(Edge *a, int start, int end) {
    int root = start;
    while (2 * root + 1 <= end) {
        int child = 2 * root + 1;
        int swap = root;
        if (a[swap].w < a[child].w) swap = child;
        if (child + 1 <= end && a[swap].w < a[child + 1].w) swap = child + 1;
        if (swap == root) return;
        Edge t = a[root]; a[root] = a[swap]; a[swap] = t;
        root = swap;
    }
}

static void sort_edges(Edge *a, int n) {
    for (int start = (n - 2) / 2; start >= 0; start--)
        sift_down(a, start, n - 1);
    for (int end = n - 1; end > 0; end--) {
        Edge t = a[0]; a[0] = a[end]; a[end] = t;
        sift_down(a, 0, end - 1);
    }
}

static int kruskal(const AdjList *g, Edge *mst, long long *cost) {
    int m = g->edgeCount;
    Edge *list = (Edge *)malloc(sizeof(Edge) * m);
    int parent[V], rnk[V];
    int k = 0, cnt = 0;
    if (!list) { fprintf(stderr, "malloc failed\n"); exit(1); }

    for (int u = 0; u < V; u++) {
        for (const AdjNode *p = g->head[u]; p; p = p->next) {
            if (u < p->to) {
                list[k].u = u;
                list[k].v = p->to;
                list[k].w = p->w;
                k++;
            }
        }
    }

    sort_edges(list, k);

    for (int i = 0; i < V; i++) { parent[i] = i; rnk[i] = 0; }

    *cost = 0;
    for (int i = 0; i < k && cnt < V - 1; i++) {
        int a = uf_find(parent, list[i].u);
        int b = uf_find(parent, list[i].v);
        if (a == b) continue;
        if (rnk[a] < rnk[b]) { int t = a; a = b; b = t; }
        parent[b] = a;
        if (rnk[a] == rnk[b]) rnk[a]++;
        mst[cnt++] = list[i];
        *cost += list[i].w;
    }

    free(list);
    return cnt;
}

static int prim(const AdjMatrix *g, Edge *mst, long long *cost) {
    int  key[V], parent[V];
    char visited[V];
    int  cnt = 0;

    for (int i = 0; i < V; i++) {
        key[i] = INT_MAX;
        parent[i] = -1;
        visited[i] = 0;
    }
    key[0] = 0;

    *cost = 0;
    for (int iter = 0; iter < V; iter++) {
        int u = -1, best = INT_MAX;
        for (int i = 0; i < V; i++) {
            if (!visited[i] && key[i] < best) {
                best = key[i];
                u = i;
            }
        }
        if (u == -1) break;

        visited[u] = 1;
        if (parent[u] != -1) {
            mst[cnt].u = parent[u];
            mst[cnt].v = u;
            mst[cnt].w = key[u];
            cnt++;
            *cost += key[u];
        }

        for (int v = 0; v < V; v++) {
            int w = g->matrix[u][v];
            if (w > 0 && !visited[v] && w < key[v]) {
                key[v] = w;
                parent[v] = u;
            }
        }
    }
    return cnt;
}

static long long now_ns(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (long long)ts.tv_sec * 1000000000LL + ts.tv_nsec;
}

static size_t mem_kruskal(int m) {
    size_t graph = sizeof(((AdjList *)0)->head)
                 + sizeof(AdjNode) * 2 * (size_t)m;
    size_t aux   = sizeof(Edge) * (size_t)m
                 + sizeof(int) * V * 2
                 + sizeof(Edge) * (V - 1);
    return graph + aux;
}

static size_t mem_prim(void) {
    size_t graph = sizeof(((AdjMatrix *)0)->matrix);
    size_t aux   = sizeof(int) * V * 2
                 + sizeof(char) * V
                 + sizeof(Edge) * (V - 1);
    return graph + aux;
}

static long long run_case(int caseNo, const char *title, int m,
                          int useKruskal, const AdjList *al, const AdjMatrix *am) {
    Edge mst[V - 1];
    long long cost = 0;
    int cnt;

    long long t0 = now_ns();
    cnt = useKruskal ? kruskal(al, mst, &cost) : prim(am, mst, &cost);
    long long t1 = now_ns();

    size_t mem = useKruskal ? mem_kruskal(m) : mem_prim();

    printf("Case %d : %s\n", caseNo, title);
    printf("Vertices      : %d\n", V);
    printf("Edges         : %d\n", m);
    printf("MST Edges     : %d\n", cnt);
    printf("MST Cost      : %lld\n", cost);
    printf("Memory        : %zu Bytes\n", mem);
    printf("Execution Time: %.6f ms\n", (t1 - t0) / 1e6);
    if (g_print_edges) {
        printf("MST Edge List :\n");
        for (int i = 0; i < cnt; i++)
            printf("  %2d - %2d (weight %3d)\n", mst[i].u, mst[i].v, mst[i].w);
    }
    if (caseNo != 4) printf("\n");
    return cost;
}

int main(int argc, char *argv[]) {
    unsigned int seed = (argc > 1) ? (unsigned int)strtoul(argv[1], NULL, 10)
                                   : (unsigned int)time(NULL);
    g_print_edges = (argc > 2);
    srand(seed);

    static Edge sparseEdges[SPARSE_E], denseEdges[DENSE_E];
    generate_graph(sparseEdges, SPARSE_E);
    generate_graph(denseEdges, DENSE_E);

    AdjList   sparseList, denseList;
    AdjMatrix sparseMat,  denseMat;
    build_adj_list(&sparseList, sparseEdges, SPARSE_E);
    build_adj_list(&denseList,  denseEdges,  DENSE_E);
    build_adj_matrix(&sparseMat, sparseEdges, SPARSE_E);
    build_adj_matrix(&denseMat,  denseEdges,  DENSE_E);

    long long c1 = run_case(1, "Sparse Graph - Adjacency List - Kruskal",
                            SPARSE_E, 1, &sparseList, NULL);
    long long c2 = run_case(2, "Dense Graph - Adjacency List - Kruskal",
                            DENSE_E, 1, &denseList, NULL);
    long long c3 = run_case(3, "Sparse Graph - Adjacency Matrix - Prim",
                            SPARSE_E, 0, NULL, &sparseMat);
    long long c4 = run_case(4, "Dense Graph - Adjacency Matrix - Prim",
                            DENSE_E, 0, NULL, &denseMat);

    free(sparseList.pool);
    free(denseList.pool);
    return (c1 == c3 && c2 == c4) ? 0 : 1;
}
