import java.util.Random;

public class TarjansAlgorithmArrayIterativeCleanStack {

    public int GRAPH_SIZE;
    public int[][] graph;
    int currentDFSNumber;
    public int[] dfsNumbers;
    public int[] lowlinkNumbers;
    public boolean onStack[];
    public int stackPointer;
    public int[] stack;
    public int currentComponent;
    public int[] components;
    public boolean[][] reachMatrix;



    public void floydWarshall() {
        // copy direct reachable nodes from graph
        for (int i = 0; i < GRAPH_SIZE; i++) {
            for (int j : graph[i]) {
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
      @ ensures (\forall int i; 0 <= i < GRAPH_SIZE; components[i] != -1);
      @ ensures (\forall int i; 0 <= i < GRAPH_SIZE;
      @             (\forall int j; i < j < GRAPH_SIZE; components[i] == components[j] ==> (reachMatrix[i][j] && reachMatrix[j][i])) &&
      @             !(\exists int k; i < k < GRAPH_SIZE; components[i] != components[k] && reachMatrix[i][k] && reachMatrix[k][i])
      @         );
      @*/
    public void startTarjans() {

        GRAPH_SIZE = 4
        ;
        // create arrays
        graph = new int[GRAPH_SIZE][GRAPH_SIZE];
        dfsNumbers = new int[GRAPH_SIZE];
        lowlinkNumbers = new int[GRAPH_SIZE];
        stack = new int[GRAPH_SIZE];
        onStack = new boolean[GRAPH_SIZE];
        components = new int[GRAPH_SIZE];
        reachMatrix = new boolean[GRAPH_SIZE][GRAPH_SIZE];

        // create random graph
        for (int i = 0; i < GRAPH_SIZE; i++) {
            for (int j = 0; j < GRAPH_SIZE; j++) {
                int rngB = nondetInt();
                if (rngB < 0) {
                    rngB = 0;
                }

                if (rngB >= GRAPH_SIZE) {
                    rngB = GRAPH_SIZE - 1;
                }
                graph[i][j] = rngB;
            }


            dfsNumbers[i] = -1;
            lowlinkNumbers[i] = -1;
            components[i] = -1;
        }


        stackPointer = 0;
        currentDFSNumber = 0;
        currentComponent = 0;

        floydWarshall();

        for (int i = 0; i < dfsNumbers.length; i++) {
            if (dfsNumbers[i] == -1) {
                this.dfs(i);
            }
        }


    }

    public void preDFS(int vertexLabel) {
        // pre process
        dfsNumbers[vertexLabel] = currentDFSNumber;
        lowlinkNumbers[vertexLabel] = currentDFSNumber;
        currentDFSNumber++;

        stack[stackPointer] = vertexLabel;
        onStack[vertexLabel] = true;
        stackPointer++;
    }

    public void postDFS(int vertexLabel) {
        if (dfsNumbers[vertexLabel] == lowlinkNumbers[vertexLabel]) {
            while (stackPointer != 0 && dfsNumbers[stack[stackPointer - 1]] >= dfsNumbers[vertexLabel]) {
                stackPointer -= 1;
                this.components[stack[stackPointer]] = currentComponent;
                onStack[stack[stackPointer]] = false;
            }
            currentComponent++;
        }

    }

    public void dfs(int startingLabel) {
        int[] backtrackStack = new int[GRAPH_SIZE];
        boolean[] onBacktrackStack = new boolean[GRAPH_SIZE];
        int[] backtrackStackElementPosition = new int[GRAPH_SIZE];
        int[] parent = new int[GRAPH_SIZE];
        for (int i = 0; i < parent.length; i++) {
            parent[i] = i;
        }

        boolean[] cleared = new boolean[GRAPH_SIZE];
        // put on stack
        int backtrackStackPointer = 0;
        backtrackStack[0] = startingLabel;
        onBacktrackStack[startingLabel] = true;

        while (backtrackStackPointer != -1) {
            int currentLabel = backtrackStack[backtrackStackPointer];
            // first visit
            if (dfsNumbers[currentLabel] == -1) {
                preDFS(currentLabel);

                for (int neighborVertexInd : graph[currentLabel]) {
                    // no visit yet and also not on backtrack stack
                    if (dfsNumbers[neighborVertexInd] == -1) {
                        if (onBacktrackStack[neighborVertexInd]) {
                            // clean onBacktrackStack to minimize unwinds
                            for (int i = backtrackStackElementPosition[neighborVertexInd]; i < backtrackStackPointer; i++) {
                                backtrackStack[i] = backtrackStack[i + 1];
                                backtrackStackElementPosition[backtrackStack[i + 1]] = i;
                            }
                            backtrackStackPointer--;
                        }
                        parent[neighborVertexInd] = currentLabel;
                        backtrackStack[++backtrackStackPointer] = neighborVertexInd;
                        onBacktrackStack[neighborVertexInd] = true;
                        backtrackStackElementPosition[neighborVertexInd] = backtrackStackPointer;
                        // visited already
                    } else if (dfsNumbers[neighborVertexInd] != -1 && dfsNumbers[neighborVertexInd] < dfsNumbers[currentLabel] && onStack[neighborVertexInd]) {
                        lowlinkNumbers[currentLabel] = lowlinkNumbers[currentLabel] <= dfsNumbers[neighborVertexInd] ? lowlinkNumbers[currentLabel] : dfsNumbers[neighborVertexInd];
                    }

                }

            } // second visit --> returned from neigbors
            else {
                // update parent lowlink
                if (!cleared[currentLabel]) {
                    lowlinkNumbers[parent[currentLabel]] = lowlinkNumbers[parent[currentLabel]] <= lowlinkNumbers[currentLabel] ? lowlinkNumbers[parent[currentLabel]] : lowlinkNumbers[currentLabel];

                    postDFS(currentLabel);
                    onBacktrackStack[currentLabel] = false;
                    cleared[currentLabel] = true;
                }
                backtrackStackPointer--;
            }

        }

    }


}
