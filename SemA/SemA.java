package SemA;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Stack;

public class SemA {

    static int nodeId = 0;
    static int scopeNodeId = 0;
    // nodes used to analyze input
    static class Node {
        int id;
        String label;
        List<Node> children = new ArrayList<>();

        // variables important for output
        int row = -1;
        String lexValue = null;

        // expression attributes
        Type type;
        Type itype; // inherited type - type of parent
        boolean lvalue;

        public Node() {
            this.id = nodeId++;
        }
    }

    static class scopeNode {
        int id;
        HashMap<String, Symbol> localVariables = new HashMap<>();
        scopeNode parent;

        public scopeNode(scopeNode parent) {
            this.id = scopeNodeId++;
            this.parent = parent;
        }

    }

    static class Type {
        enum Basic {INT, CHAR, VOID};

        Basic basic;
        boolean isSequence = false;
        boolean isConst = false;

        Type(Basic basic) {
            this.basic = basic;
        }
    }

    static class Symbol {
        String name;
        Type type;

        Symbol(String name, Type type) {
            this.name = name;
            this.type = type;
        }
    }

    private static int depth(String line){
        int i = 0;
        while (i < line.length() && line.charAt(i) == ' ') i++;
        return i;
    }

    private static Node parseLine(String line){
        line =  line.trim();
        String[] parts = line.split(" ");

        Node node = new Node();
        node.label = parts[0];

        // if row contains terminated
        if (!parts[0].startsWith("<")){
            // epsilon row (empty)
            if (parts[0].equals("$")) return node;

            // row number is the second part of the line
            node.row = Integer.parseInt(parts[1]);

            // lexvalue is the rest of the line
            StringBuilder sb = new StringBuilder();
            for (int i = 2; i < parts.length; i++){
                sb.append(parts[i]);
                if (i < parts.length-1) sb.append(" ");
            }
            node.lexValue = sb.toString();
        }

        return node;
    }

    // parse tree from sintax analysis output
    private static Node loadTree() throws IOException{
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
        String line;
        Stack<Node> stack= new Stack<>();
        Node root = null;

        while ((line = br.readLine()) != null) {
            if (line.isEmpty()) continue;

            int d = depth(line);
            Node node = parseLine(line);

            // get to the right level (depth)
            while (stack.size() > d){
                stack.pop();
            }

            if (stack.isEmpty()){
                // node becomes the root
                root = node;
            }else{
                // node becomes a child of the last node on the stack
                stack.peek().children.add(node);
            }
            stack.push(node);

        }

        return root;
    }

    static Stack<scopeNode> scopeStack = new Stack<>();

    private static scopeNode newScope() {
        scopeNode parent = null;
        if (!scopeStack.isEmpty()){
            parent = scopeStack.peek();
        }
        scopeNode ns = new scopeNode(parent);
        scopeStack.push(ns);
        return ns;
    }

    static void ispisiStablo(Node c, int dubina) {
        System.out.print(" ".repeat(dubina));
        System.out.println(c.id +
                (c.lexValue != null ? " (" + c.lexValue + ")" : "")
        );

        for (Node dijete : c.children) {
            ispisiStablo(dijete, dubina + 1);
        }
    }

    static void process(Node node){
        if (node.label.equals("<prijevodna_jedinica>")) {
            if (node.children.size()==1){
                process(node.children.get(0));
                return;
            }else if (node.children.size()==2){
                process(node.children.get(0));
                process(node.children.get(1));
                return;
            }
        }

        if (node.label.equals("<deklaracija>")){
            Node imeTipa = node.children.get(0);
            Node listaInitDek = node.children.get(1);

            process(imeTipa);

            listaInitDek.itype = imeTipa.type;
            process(listaInitDek);
            return;
        }

        if (node.label.equals("<ime_tipa>")){
            if (node.children.size()==1){
                Node spec = node.children.get(0);
                node.type = spec.type;
                process(spec);
                return;
            }else if (node.children.size()==2){
                Node spec = node.children.get(1);
                Type t = new Type(spec.type.basic);
                t.isSequence = spec.type.isSequence;
                t.isConst = true;

                node.type = t;

                if (spec.type.basic == Type.Basic.VOID){
                    //error()
                }
                return;
            }
        }

        if (node.label.equals("<specifikator_tipa>")){
            if (node.children.get(0).equals("KR_VOID")){
                node.type = new Type(Type.Basic.VOID);
            }else if (node.children.get(0).equals("KR_INT")){
                node.type = new Type(Type.Basic.INT);
            }else if (node.children.get(0).equals("KR_CHAR")){
                node.type = new Type(Type.Basic.CHAR);
            }
            return;
        }

        for (Node child : node.children)
            process(child);
    }

    public static void main(String[] args) {
        Node root = null;
        try {
            root = loadTree();
        } catch (IOException e) {
            e.printStackTrace();
        }

        ispisiStablo(root, 0);
        process(root);
    }
}
