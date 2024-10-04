import java.util.Random;

public class TarjansAlgorithmListIterativeCleanStack {
    class LinkedList {
        Node head;
        int size;

        class Node {
            public int value;
            public Node next;

            Node(int value) {
                this.value = value;
                this.next = null;
            }
        }

        LinkedList() {
            this.head = null;
            this.size = 0;
        }

        public void insert(int value) {
            Node node = new Node(value);

            if (this.head == null) {
                this.head = node;
            } else {
                Node last = this.head;
                while (last.next != null) {
                    last = last.next;
                }
                last.next = node;
            }

            size++;
        }

        public int get(int i) {
            Node resultNode = head;
            for (int k = 0; k < i; k++) {
                resultNode = resultNode.next;
            }
            return resultNode.value;
        }

        public int size() {
            return size;
        }
    }



    public int GRAPH_SIZE;
    public LinkedList[] graph;
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
            for (int j = 0; j < GRAPH_SIZE; j++) {
                reachMatrix[i][graph[i].get(j)] = true;
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
      @             !(\exists int j; i < j < GRAPH_SIZE; components[i] != components[j] && reachMatrix[i][j] && reachMatrix[j][i])
      @         );
      @*/
    public void startTarjans() {
        GRAPH_SIZE = 2;

        // create arrays
        graph = new LinkedList[GRAPH_SIZE];
        dfsNumbers = new int[GRAPH_SIZE];
        lowlinkNumbers = new int[GRAPH_SIZE];
        stack = new int[GRAPH_SIZE];
        onStack = new boolean[GRAPH_SIZE];
        components = new int[GRAPH_SIZE];
        reachMatrix = new boolean[GRAPH_SIZE][GRAPH_SIZE];


        // create random graph
        for (int i = 0; i < GRAPH_SIZE; i++) {
            LinkedList neighborHood = new LinkedList();

            for (int j = 0; j < GRAPH_SIZE; j++) {
                int rngB = nondetInt();
                if (rngB < 0) {
                    rngB = 0;
                }
                if (rngB >= GRAPH_SIZE) {
                    rngB = GRAPH_SIZE - 1;
                }
                neighborHood.insert(rngB);
            }
            graph[i] = neighborHood;

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
        int[] backtrackStack = new int[GRAPH_SIZE * GRAPH_SIZE];
        boolean[] onBacktrackStack = new boolean[GRAPH_SIZE];
        int[] parent = new int[GRAPH_SIZE];
        for (int i = 0; i < GRAPH_SIZE; i++) {
            parent[i] = i;
        }
        boolean[] cleared = new boolean[GRAPH_SIZE];
        int[] backtrackStackElementPosition = new int[GRAPH_SIZE];
        // put on stack
        int backtrackStackPointer = 0;
        backtrackStack[0] = startingLabel;
        onBacktrackStack[startingLabel] = true;

        while (backtrackStackPointer != -1) {
            int currentLabel = backtrackStack[backtrackStackPointer];
            // first visit
            if (dfsNumbers[currentLabel] == -1) {
                preDFS(currentLabel);

                LinkedList neighborHood = graph[currentLabel];
                for (int neighborVertexInd = 0; neighborVertexInd < neighborHood.size(); neighborVertexInd++) {
                    int neighborVertex = neighborHood.get(neighborVertexInd);
                    // no visit yet and also not on backtrack stack
                    if (dfsNumbers[neighborVertex] == -1) {

                        if (onBacktrackStack[neighborVertex]) {
                            // clean onBacktrackStack to minimize unwinds
                            for (int i = backtrackStackElementPosition[neighborVertex]; i < backtrackStackPointer; i++) {
                                backtrackStack[i] = backtrackStack[i + 1];
                                backtrackStackElementPosition[backtrackStack[i + 1]] = i;
                            }
                            backtrackStackPointer--;
                        }

                        parent[neighborVertex] = currentLabel;
                        backtrackStack[++backtrackStackPointer] = neighborVertex;
                        onBacktrackStack[neighborVertex] = true;
                        backtrackStackElementPosition[neighborVertex] = backtrackStackPointer;
                        // visited already
                    } else if (dfsNumbers[neighborVertex] != -1 && dfsNumbers[neighborVertex] < dfsNumbers[currentLabel] && onStack[neighborVertex]) {
                        lowlinkNumbers[currentLabel] = lowlinkNumbers[currentLabel] <= dfsNumbers[neighborVertex] ? lowlinkNumbers[currentLabel] : dfsNumbers[neighborVertex];
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
