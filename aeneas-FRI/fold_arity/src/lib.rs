
#![no_std]

extern crate alloc;


// function chooses how much we should fold in current round
pub fn compute_log_arity_for_round(
    log_current_height: usize,
    next_input_log_height: Option<usize>,
    log_final_height: usize,
    max_log_arity: usize,
) -> usize {
    // suppose (as in original code), log_current_height > log_final_height
    let max_fold_to_target = log_current_height - log_final_height;

    let max_fold = match next_input_log_height {
        None => max_fold_to_target,
        Some(next_log_height) => {
            let max_fold_to_next = log_current_height - next_log_height;
            if max_fold_to_next < max_fold_to_target {
                max_fold_to_next
            } else {
                max_fold_to_target
            }
        }
    };

    if max_fold < max_log_arity { max_fold } else { max_log_arity }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_bounds() {
        let r = compute_log_arity_for_round(10, Some(8), 3, 4);
        assert!(r <= 4);
    }
}

