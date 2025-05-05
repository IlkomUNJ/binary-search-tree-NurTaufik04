use std::cell::RefCell;
use std::rc::{Rc, Weak};

pub type BstNodeLink = Rc<RefCell<BstNode>>;
pub type WeakBstNodeLink = Weak<RefCell<BstNode>>;

//this package implement BST wrapper
#[derive(Debug, Clone)]
pub struct BstNode {
    pub key: Option<i32>,
    pub parent: Option<WeakBstNodeLink>,
    pub left: Option<BstNodeLink>,
    pub right: Option<BstNodeLink>,
}

impl BstNode {
    //private interface
    fn new(key: i32) -> Self {
        BstNode {
            key: Some(key),
            left: None,
            right: None,
            parent: None,
        }
    }

    pub fn new_bst_nodelink(value: i32) -> BstNodeLink {
        let currentnode = BstNode::new(value);
        let currentlink = Rc::new(RefCell::new(currentnode));
        currentlink
    }

    /**
     * Get a copy of node link
     */
    pub fn get_bst_nodelink_copy(&self) -> BstNodeLink {
        Rc::new(RefCell::new(self.clone()))
    }

    fn downgrade(node: &BstNodeLink) -> WeakBstNodeLink {
        Rc::<RefCell<BstNode>>::downgrade(node)
    }

    //private interface
    fn new_with_parent(parent: &BstNodeLink, value: i32) -> BstNodeLink {
        let mut currentnode = BstNode::new(value);
        //currentnode.add_parent(Rc::<RefCell<BstNode>>::downgrade(parent));
        currentnode.parent = Some(BstNode::downgrade(parent));
        let currentlink = Rc::new(RefCell::new(currentnode));
        currentlink
    }

    //add new left child, set the parent to current_node_link
    pub fn add_left_child(&mut self, current_node_link: &BstNodeLink, value: i32) {
        let new_node = BstNode::new_with_parent(current_node_link, value);
        self.left = Some(new_node);
    }

    //add new left child, set the parent to current_node_link
    pub fn add_right_child(&mut self, current_node_link: &BstNodeLink, value: i32) {
        let new_node = BstNode::new_with_parent(current_node_link, value);
        self.right = Some(new_node);
    }

    //search the current tree which node fit the value
    pub fn tree_search(&self, value: &i32) -> Option<BstNodeLink> {
        let mut current = Some(self.get_bst_nodelink_copy());

        while let Some(node_link) = current {
            let node = node_link.borrow();
            if node.key.is_none() {
                return None;
            }
            let node_key = node.key.unwrap();
            if *value == node_key {
                return Some(node_link.clone());
            } else if *value < node_key {
                current = node.left.clone();
            } else {
                current = node.right.clone();
            }
        }
        None
    }

    /**seek minimum by recurs
     * in BST minimum always on the left
     */
     pub fn minimum(&self) -> BstNodeLink {
        let mut current = self.get_bst_nodelink_copy();
        loop {
            let left = current.borrow().left.clone();
            if left.is_none() {
                return current;
            }
            current = left.unwrap();
        }
    }

    pub fn maximum(&self) -> BstNodeLink {
        let mut current = self.get_bst_nodelink_copy();
        loop {
            let right = current.borrow().right.clone();
            if right.is_none() {
                return current;
            }
            current = right.unwrap();
        }
    }

    /**
     * Return the root of a node, return self if not exist
     */
    pub fn get_root(node: &BstNodeLink) -> BstNodeLink {
        let parent = BstNode::upgrade_weak_to_strong(node.borrow().parent.clone());
        if parent.is_none() {
            return node.clone();
        }
        return BstNode::get_root(&parent.unwrap());
    }

    /**
     * NOTE: Buggy from pull request
     * Find node successor according to the book
     * Should return None, if x_node is the highest key in the tree
     */
     pub fn tree_successor(x_node: &BstNodeLink) -> BstNodeLink {
        let x_ref = x_node.borrow();
        if let Some(right) = x_ref.right.clone() {
            return right.borrow().minimum();
        }
        drop(x_ref); // important to release borrow before mutate x_node
        let mut x = x_node.clone();
        let mut y_opt = BstNode::upgrade_weak_to_strong(x.borrow().parent.clone());
        while let Some(y) = y_opt.clone() {
            if Rc::ptr_eq(&x, &y.borrow().left.clone().unwrap_or_else(|| BstNode::new_bst_nodelink(0))) {
                return y;
            }
            x = y;
            y_opt = BstNode::upgrade_weak_to_strong(x.borrow().parent.clone());
        }
        x_node.clone() // return self if no successor (means x is the maximum node)
    }

    /**
     * Alternate simpler version of tree_successor that made use of is_nil checking
     */
    #[allow(dead_code)]
    pub fn tree_successor_simpler(x_node: &BstNodeLink) -> Option<BstNodeLink>{
        //create a shadow of x_node so it can mutate
        let mut x_node = x_node;
        let right_node = &x_node.borrow().right.clone();
        if BstNode::is_nil(right_node)!=true{
            return Some(right_node.clone().unwrap().borrow().minimum());
        }

        let mut y_node = BstNode::upgrade_weak_to_strong(x_node.borrow().parent.clone());
        let y_node_right = &y_node.clone().unwrap().borrow().right.clone();
        let mut y_node2: Rc<RefCell<BstNode>>;
        while BstNode::is_nil(&y_node) && BstNode::is_node_match_option(Some(x_node.clone()), y_node_right.clone()) {
            y_node2 = y_node.clone().unwrap();
            x_node = &y_node2;
            let y_parent = y_node.clone().unwrap().borrow().parent.clone().unwrap();
            y_node = BstNode::upgrade_weak_to_strong(Some(y_parent));
        }

        //in case our sucessor traversal yield root, means self is the highest key
        if BstNode::is_node_match_option(y_node.clone(), Some(BstNode::get_root(&x_node))) {
            return None;
        }

        //default return self / x_node
        return Some(y_node.clone().unwrap())
    }

    /**
     * private function return true if node doesn't has parent nor children nor key
     */
    fn is_nil(node: &Option<BstNodeLink>) -> bool {
        match node {
            None => true,
            Some(x) => {
                if x.borrow().parent.is_none()
                    || x.borrow().left.is_none()
                    || x.borrow().right.is_none()
                {
                    return true;
                }
                return false;
            }
        }
    }

    //helper function to compare both nodelink
    fn is_node_match_option(node1: Option<BstNodeLink>, node2: Option<BstNodeLink>) -> bool {
        if node1.is_none() && node2.is_none() {
            return true;
        }
        if let Some(node1v) = node1 {
            return node2.is_some_and(|x: BstNodeLink| x.borrow().key == node1v.borrow().key);
        }
        return false;
    }

    fn is_node_match(anode: &BstNodeLink, bnode: &BstNodeLink) -> bool {
        if anode.borrow().key == bnode.borrow().key {
            return true;
        }
        return false;
    }

    /**
     * As the name implied, used to upgrade parent node to strong nodelink
     */
    fn upgrade_weak_to_strong(node: Option<WeakBstNodeLink>) -> Option<BstNodeLink> {
        match node {
            None => None,
            Some(x) => Some(x.upgrade().unwrap()),
        }
    }

    pub fn tree_insert(root: &BstNodeLink, key: i32) {
        let z = BstNode::new_bst_nodelink(key);
        let mut y: Option<BstNodeLink> = None;
        let mut x = Some(Rc::clone(root));
    
        while let Some(current) = x.take() { // Take ownership of the Option
            y = Some(Rc::clone(&current));
            let current_borrowed = current.borrow();
    
            if key < current_borrowed.key.unwrap() {
                x = current_borrowed.left.clone();
            } else {
                x = current_borrowed.right.clone();
            }
        }
    
        z.borrow_mut().parent = y.as_ref().map(Rc::downgrade);
    
        if let Some(ref y_node) = y {
            if key < y_node.borrow().key.unwrap() {
                y_node.borrow_mut().left = Some(Rc::clone(&z));
            } else {
                y_node.borrow_mut().right = Some(Rc::clone(&z));
            }
        }
    }

    pub fn transplant(u: &BstNodeLink, v: Option<BstNodeLink>) {
        if let Some(parent_weak) = &u.borrow().parent {
            if let Some(parent) = parent_weak.upgrade() {
                if parent.borrow().left.as_ref().map(|x| Rc::ptr_eq(x, u)).unwrap_or(false) {
                    parent.borrow_mut().left = v.clone();
                } else {
                    parent.borrow_mut().right = v.clone();
                }
                if let Some(ref v_node) = v {
                    v_node.borrow_mut().parent = Some(Rc::downgrade(&parent));
                }
            }
        }
    }

    pub fn tree_delete(root: &BstNodeLink, key: i32) {
        if let Some(node) = root.borrow().tree_search(&key) {
            let left = node.borrow().left.clone();
            let right = node.borrow().right.clone();

            if left.is_none() {
                BstNode::transplant(&node, right);
            } else if right.is_none() {
                BstNode::transplant(&node, left);
            } else {
                let min_right = right.as_ref().unwrap().borrow().minimum();
                if min_right.borrow().parent.as_ref().unwrap().upgrade().unwrap().as_ptr()
                    != node.as_ptr()
                {
                    BstNode::transplant(&min_right, min_right.borrow().right.clone());
                    min_right.borrow_mut().right = right.clone();
                    if let Some(ref r) = right {
                        r.borrow_mut().parent = Some(Rc::downgrade(&min_right));
                    }
                }
                BstNode::transplant(&node, Some(Rc::clone(&min_right)));
                min_right.borrow_mut().left = left.clone();
                if let Some(ref l) = left {
                    l.borrow_mut().parent = Some(Rc::downgrade(&min_right));
                }
            }
        }
    }
}
