import pandas as pd
import os
import glob
import numpy as np

def process_gesture_data(data_folder='data'):
    """
    Process gesture data CSV files:
    1. Keep 6 raw data columns (GX_Raw, GY_Raw, GZ_Raw, AX_Raw, AY_Raw, AZ_Raw) with Gesture_Index and Gesture
    2. Keep only 50 samples per Gesture_Index (center cropping)
    3. Convert gesture categories to numeric labels
    4. Merge all CSV files
    """
    
    # Get all CSV files in data folder
    csv_pattern = os.path.join(data_folder, '*.csv')
    csv_files = glob.glob(csv_pattern)
    
    if not csv_files:
        print(f"Error: No CSV files found in '{data_folder}' folder")
        return None
    
    print(f"Found CSV files ({len(csv_files)}):")
    for f in csv_files:
        print(f"  - {os.path.basename(f)}")
    
    # Define columns to keep
    columns_to_keep = ['Gesture_Index', 'Gesture', 'GX_Raw', 'GY_Raw', 'GZ_Raw', 
                       'AX_Raw', 'AY_Raw', 'AZ_Raw']
    
    all_processed_data = []
    
    for file in csv_files:
        print(f"\nProcessing file: {os.path.basename(file)}")
        
        try:
            df = pd.read_csv(file)
        except Exception as e:
            print(f"  Error: Cannot read file - {e}")
            continue
        
        # Check if necessary columns exist
        missing_cols = [col for col in columns_to_keep if col not in df.columns]
        if missing_cols:
            print(f"  Error: Missing columns {missing_cols}")
            continue
        
        # 1. Keep specified columns
        df = df[columns_to_keep].copy()
        
        # 2. Keep only 50 samples per Gesture_Index (center cropping)
        processed_groups = []
        
        for gesture_idx, group in df.groupby('Gesture_Index'):
            n_samples = len(group)
            
            if n_samples > 50:
                # Calculate number of samples to crop
                excess = n_samples - 50
                start_cut = excess // 2  # Crop from beginning
                end_cut = excess - start_cut  # Crop from end
                
                # Keep middle 50 samples
                group = group.iloc[start_cut:start_cut + 50].copy()
                print(f"  Gesture_Index {gesture_idx}: {n_samples} -> 50 (crop front {start_cut}, crop back {end_cut})")
            else:
                print(f"  Gesture_Index {gesture_idx}: {n_samples} samples (less than 50, keeping all)")
            
            processed_groups.append(group)
        
        # Merge all groups from this file
        if processed_groups:
            df_processed = pd.concat(processed_groups, ignore_index=True)
            all_processed_data.append(df_processed)
    
    if not all_processed_data:
        print("Error: No data was successfully processed")
        return None
    
    # Merge all files data
    final_df = pd.concat(all_processed_data, ignore_index=True)
    
    # 3. Convert gesture categories to numeric labels
    gesture_mapping = {gesture: idx for idx, gesture in enumerate(final_df['Gesture'].unique())}
    final_df['Gesture_Label'] = final_df['Gesture'].map(gesture_mapping)
    
    # Remove original Gesture column, keep numeric label
    final_df = final_df.drop('Gesture', axis=1)
    
    # Adjust column order: Gesture_Index, Gesture_Label, then 6 raw data columns
    column_order = ['Gesture_Index', 'Gesture_Label', 'GX_Raw', 'GY_Raw', 'GZ_Raw', 
                    'AX_Raw', 'AY_Raw', 'AZ_Raw']
    final_df = final_df[column_order]
    
    print(f"\nFinal dataset information:")
    print(f"  Total samples: {len(final_df)}")
    print(f"  Number of classes: {len(gesture_mapping)}")
    print(f"  Columns: {list(final_df.columns)}")
    
    # Save merged file
    output_file = 'merged_gesture_data.csv'
    final_df.to_csv(output_file, index=False)
    print(f"\nSaved merged file: {output_file}")
    
    # Output class mapping at the end
    print("\n" + "="*50)
    print("Class Mapping (Gesture -> Numeric Label):")
    print("="*50)
    for gesture, label in sorted(gesture_mapping.items(), key=lambda x: x[1]):
        count = (final_df['Gesture_Label'] == label).sum()
        print(f"  {label}: {gesture} (Total: {count} samples)")
    
    return final_df


if __name__ == '__main__':
    # Process data in the 'data' folder
    result = process_gesture_data('data')
    
    # if result is not None:
        # print("\nData preview (first 10 rows):")
        # print(result.head(10))