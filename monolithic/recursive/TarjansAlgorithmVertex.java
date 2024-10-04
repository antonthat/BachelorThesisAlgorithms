import java.util.Random;

public class TarjansAlgorithmVertex {

    public int GRAPH_SIZE;
    public Vertex[] graph;
    int currentDFSNumber;
    public boolean onStack[];
    public int stackPointer;
    public int[] stack;
    public int currentComponent;
    public boolean[][] reachMatrix;

    public class Vertex {
        public int id;
        public int dfsNumber;
        public int lowlink;
        public int component;
        public int[] neighbors;
        public Vertex(int id, int[] neighborIds) {
            this.dfsNumber = -1;
            this.lowlink = -1;
            this.component = -1;
            this.id = id;
            this.neighbors = neighborIds;
        }


    }


    public void floydWarshall() {
        // copy direct reachable nodes from graph
        for (int i = 0; i < GRAPH_SIZE; i++) {
            for (int j : graph[i].neighbors) {
                reachMatrix[i][j] = true;
            }
        }

        // calculate reach matrix
        for (int k = 0; k < GRAPH_SIZE; k++) {
            for (int i = 0; i < GRAPH_SIZE; i++) {
                for (int j = 0; j < GRAPH_SIZE; j++) {
                    if (reachMatrix[i][k] && reachMatrix[k][j])
                        reachMatrix[i][j] = true;
                }
            }
        }
    }


    private int nondetInt() {
        return (new Random()).nextInt(GRAPH_SIZE);
    }

    /*@ normal_behaviour
      @ ensures (\forall int i; 0 <= i < GRAPH_SIZE; graph[i].component != -1);
      @ ensures (\forall int i; 0 <= i < GRAPH_SIZE;
      @             (\forall int j; i < j < GRAPH_SIZE; graph[i].component == graph[j].component ==> (reachMatrix[i][j] && reachMatrix[j][i])) &&
      @             !(\exists int j; i < j < GRAPH_SIZE; graph[i].component != graph[j].component && reachMatrix[i][j] && reachMatrix[j][i])
      @         );
      @*/
    public void startTarjans() {
        GRAPH_SIZE = 3;
        // create arrays
        graph = new Vertex[GRAPH_SIZE];
        stack = new int[GRAPH_SIZE];
        onStack = new boolean[GRAPH_SIZE];
        reachMatrix = new boolean[GRAPH_SIZE][GRAPH_SIZE];

        // create random graph
        for (int i = 0; i < GRAPH_SIZE; i++) {
            int[] neighbors = new int[GRAPH_SIZE];
            for (int j = 0; j < GRAPH_SIZE; j++) {
                int rngB = nondetInt();
                if (rngB < 0) {
                    rngB = 0;
                }

                if (rngB >= GRAPH_SIZE) {
                    rngB = GRAPH_SIZE - 1;
                }
                neighbors[j] = rngB;
            }
            graph[i] = new Vertex(i, neighbors);

        }

        stackPointer = 0;
        currentDFSNumber = 0;
        currentComponent = 0;

        floydWarshall();

        for (int i = 0; i < GRAPH_SIZE; i++) {
            if (graph[i].dfsNumber == -1) {
                this.dfs(i);
            }
        }
    }

    public void preDFS(int vertexLabel) {
        // pre process
        graph[vertexLabel].dfsNumber = currentDFSNumber;
        graph[vertexLabel].dfsNumber = currentDFSNumber;
        currentDFSNumber++;

        stack[stackPointer] = vertexLabel;
        onStack[vertexLabel] = true;
        stackPointer++;
    }

    public void postDFS(int vertexLabel) {
        if (graph[vertexLabel].dfsNumber == graph[vertexLabel].lowlink) {
            while (stackPointer != 0 && graph[stack[stackPointer - 1]].dfsNumber >= graph[vertexLabel].dfsNumber) {
                stackPointer -= 1;
                graph[stack[stackPointer]].component = currentComponent;
                onStack[stack[stackPointer]] = false;
            }
            currentComponent++;
        }

    }

    public void dfs(int vertexLabel) {
        preDFS(vertexLabel);

        for (int neighborVertexInd : graph[vertexLabel].neighbors) {
            if (graph[neighborVertexInd].dfsNumber == -1) {
                dfs(neighborVertexInd);
                graph[vertexLabel].lowlink = graph[vertexLabel].lowlink <= graph[neighborVertexInd].lowlink ? graph[vertexLabel].lowlink : graph[neighborVertexInd].lowlink;
            } else if (graph[neighborVertexInd].dfsNumber < graph[vertexLabel].dfsNumber && onStack[neighborVertexInd]) {
                graph[vertexLabel].lowlink = graph[vertexLabel].lowlink <= graph[neighborVertexInd].dfsNumber ? graph[vertexLabel].lowlink : graph[neighborVertexInd].dfsNumber;
            }
        }

        postDFS(vertexLabel);
    }


}
