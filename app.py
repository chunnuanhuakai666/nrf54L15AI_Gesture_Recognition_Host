import serial
import serial.tools.list_ports
import time
import re
import threading
from collections import deque
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.figure import Figure
import numpy as np
from datetime import datetime
import csv
import os
import math

# 设置字体和样式（兼容中英文）
plt.rcParams["font.family"] = ["DejaVu Sans", "SimHei"]
plt.rcParams["axes.unicode_minus"] = False

# 自定义颜色主题（专业配色）
COLORS = {
    'bg': '#f8f9fa',
    'fg': '#212529',
    'accent': '#0d6efd',
    'success': '#198754',
    'warning': '#ffc107',
    'danger': '#dc3545',
    'info': '#0dcaf0',
    'light': '#f8f9fa',
    'dark': '#212529',
    'gray': '#6c757d'
}

# 定义支持的手势标签（英文）
GESTURE_LABELS = [
    "No_Gesture", "Single_Click", "Double_Click", "Swipe_Up", "Swipe_Down", 
    "Swipe_Left", "Swipe_Right", "Rotate_Clockwise", "Rotate_Counterclockwise", 
    "Fist", "Open_Hand"
]

# 校准参数（可在程序中更新）
CALIBRATION_PARAMS = {
    'gx_offset': 0.0, 'gy_offset': 0.0, 'gz_offset': 0.0,
    'ax_offset': 0.0, 'ay_offset': 0.0, 'az_offset': 0.0
}

class CountdownWindow(tk.Toplevel):
    """倒计时窗口（带动画，优化显示逻辑）"""
    def __init__(self, parent, count=3, title="Prepare for Sampling"):
        super().__init__(parent)
        self.parent = parent
        self.count = count
        self.current_count = count
        self.title(title)
        self.geometry("400x250")
        self.resizable(False, False)
        self.configure(bg='white')
        self.transient(parent)
        self.grab_set()  # 模态窗口
        self.attributes('-topmost', True)  # 置顶显示
        
        # 居中显示
        self.center_window()
        
        # 倒计时容器
        count_frame = tk.Frame(self, bg='white')
        count_frame.pack(expand=True, pady=20)
        
        # 倒计时数字（大字体+渐变）
        self.count_label = tk.Label(
            count_frame, text=str(self.current_count),
            font=('Segoe UI', 72, 'bold'),
            fg=COLORS['accent'], bg='white'
        )
        self.count_label.pack(pady=10)
        
        # 提示标签
        self.tip_label = tk.Label(
            self, text="Get ready to perform gesture...",
            font=('Segoe UI', 12), fg=COLORS['dark'], bg='white'
        )
        self.tip_label.pack(pady=5)
        
        # 进度标签
        self.progress_label = tk.Label(
            self, text="", font=('Segoe UI', 10),
            fg=COLORS['gray'], bg='white'
        )
        self.progress_label.pack(pady=5)
        
        # 按钮容器
        btn_frame = tk.Frame(self, bg='white')
        btn_frame.pack(pady=10)
        
        # 取消按钮（美化）
        self.cancel_btn = tk.Button(
            btn_frame, text="Cancel Sampling",
            font=('Segoe UI', 10, 'bold'),
            bg=COLORS['danger'], fg='white',
            relief='flat', bd=0, padx=15, pady=5,
            cursor='hand2', command=self.cancel,
            activebackground='#bb2d3b'
        )
        self.cancel_btn.pack(padx=10)
        
        self.cancelled = False
        self.finished = False
        
        # 开始倒计时
        self.update_countdown()
    
    def center_window(self):
        """窗口居中"""
        self.update_idletasks()
        x = (self.winfo_screenwidth() // 2) - (400 // 2)
        y = (self.winfo_screenheight() // 2) - (250 // 2)
        self.geometry(f"400x250+{x}+{y}")
    
    def update_countdown(self):
        """更新倒计时（优化动画）"""
        if self.cancelled:
            return
        
        if self.current_count > 0:
            # 更新数字和颜色
            self.count_label.config(
                text=str(self.current_count),
                fg=COLORS['accent'] if self.current_count > 1 else COLORS['warning']
            )
            # 更新进度文本
            self.progress_label.config(
                text=f"Sampling starts in {self.current_count} seconds..."
            )
            
            self.current_count -= 1
            self.after(1000, self.update_countdown)
        else:
            # 倒计时结束
            self.count_label.config(text="GO!", fg=COLORS['success'])
            self.tip_label.config(text="Perform gesture NOW!")
            self.progress_label.config(text="Sampling in progress...")
            self.after(800, self.finish)  # 延长显示时间
    
    def cancel(self):
        """取消采集"""
        self.cancelled = True
        self.finished = False
        self.destroy()
    
    def finish(self):
        """倒计时完成"""
        self.finished = True
        self.withdraw()
        self.after(500, self.destroy)

class BMI270GUI:
    def __init__(self, root):
        self.root = root
        self.root.title("BMI270 Sensor Data Acquisition System")
        self.root.geometry("1400x900")
        self.root.minsize(1200, 800)
        self.root.configure(bg=COLORS['bg'])
        
        # 设置样式
        self.setup_styles()
        
        # 数据相关变量
        self.serial_conn = None
        self.running = False
        self.auto_recording = False
        self.data_buffer = deque(maxlen=500)
        self.sample_counter = 0
        self.record_counter = 0
        self.current_gesture = tk.StringVar(value=GESTURE_LABELS[0])
        self.gesture_sample_count = 0
        self.calibrated = False
        
        # 自动采集相关
        self.auto_sample_times = tk.IntVar(value=25)
        self.current_auto_count = 0
        self.auto_pause_time = 3
        self.auto_cancelled = False
        
        # 校准相关
        self.calibration_data = []
        self.calibrating = False
        
        # ========== 新增：数据缓存相关变量 ==========
        self.data_cache = []  # 缓存采集的数据
        self.cache_enabled = False  # 是否启用缓存模式
        self.save_filename = None  # 保存文件名
        
        # ========== 关键修改：适配新的数据格式 ==========
        # 新格式：AX: xxx; AY: xxx; AZ: xxx; GX: xxx; GY: xxx; GZ: xxx;
        self.pattern = re.compile(
            r'AX:\s*([-+]?\d*\.?\d+);\s*'    # AX在前
            r'AY:\s*([-+]?\d*\.?\d+);\s*'    # AY
            r'AZ:\s*([-+]?\d*\.?\d+);\s*'    # AZ
            r'GX:\s*([-+]?\d*\.?\d+);\s*'    # GX在后
            r'GY:\s*([-+]?\d*\.?\d+);\s*'    # GY
            r'GZ:\s*([-+]?\d*\.?\d+);'       # GZ
        )
        # ===============================================
        
        # 初始化UI变量
        self.port_var = tk.StringVar()
        self.status_var = tk.StringVar(value="● Disconnected")
        self.auto_pause_var = tk.StringVar(value="3")
        self.record_status_var = tk.StringVar(value="⏹️ Not Recording")
        self.auto_progress_var = tk.StringVar(value="Not Started")
        self.gesture_status_var = tk.StringVar(value="No_Gesture")
        self.calib_status_var = tk.StringVar(value="Not Calibrated")
        self.calib_status_display = tk.StringVar(value="Not Calibrated")
        self.system_info_var = tk.StringVar(value="Samples: 0 | Buffer: 0/500")
        self.show_raw_var = tk.BooleanVar(value=True)
        
        # 初始化GUI
        self.setup_ui()
        
        # 启动数据读取线程
        self.read_thread = None
        
    def setup_styles(self):
        """设置现代化样式"""
        style = ttk.Style()
        style.theme_use('clam')
        
        # 自定义样式
        style.configure('Title.TLabel', 
                       font=('Segoe UI', 16, 'bold'), 
                       foreground=COLORS['dark'],
                       background=COLORS['bg'])
        
        style.configure('Card.TLabelframe', 
                       background=COLORS['bg'], 
                       relief='flat', 
                       borderwidth=0)
    
    def setup_ui(self):
        """优化界面布局"""
        # 主容器
        main_container = ttk.Frame(self.root, padding="10")
        main_container.pack(fill=tk.BOTH, expand=True)
        
        # 标题行
        title_label = ttk.Label(
            main_container, 
            text="BMI270 Sensor Data Acquisition System", 
            style='Title.TLabel'
        )
        title_label.grid(row=0, column=0, columnspan=2, sticky='ew', pady=(0, 10))
        
        # 串口控制区域
        serial_frame = self.create_card(main_container, "Serial Port Control")
        serial_frame.grid(row=1, column=0, sticky='ew', pady=(0, 10), padx=(0, 5))
        
        # 串口控制内容
        serial_content = ttk.Frame(serial_frame)
        serial_content.pack(fill=tk.X, padx=10, pady=10)
        
        # 串口选择
        ttk.Label(serial_content, text="Port:", font=('Segoe UI', 10, 'bold')).grid(row=0, column=0, sticky='w', padx=(0, 5))
        self.port_combo = ttk.Combobox(serial_content, textvariable=self.port_var, width=15, font=('Segoe UI', 9))
        self.port_combo.grid(row=0, column=1, sticky='w', padx=(0, 10))
        
        self.refresh_btn = self.create_button(serial_content, "🔄 Refresh", COLORS['accent'], command=self.refresh_ports)
        self.refresh_btn.grid(row=0, column=2, sticky='w')
        
        # 连接按钮
        self.connect_btn = self.create_button(serial_content, "🔌 Connect", COLORS['success'], command=self.connect)
        self.connect_btn.grid(row=1, column=0, sticky='w', pady=(10, 0), padx=(0, 5))
        
        self.disconnect_btn = self.create_button(serial_content, "⚡ Disconnect", COLORS['warning'], command=self.disconnect, state='disabled')
        self.disconnect_btn.grid(row=1, column=1, sticky='w', pady=(10, 0))
        
        # 状态显示
        status_label = ttk.Label(serial_content, textvariable=self.status_var, font=('Segoe UI', 10, 'bold'), foreground=COLORS['danger'])
        status_label.grid(row=1, column=2, sticky='w', pady=(10, 0), padx=(10, 0))
        
        # 手势控制区域
        gesture_frame = self.create_card(main_container, "Gesture & Auto Sampling")
        gesture_frame.grid(row=1, column=1, sticky='ew', pady=(0, 10), padx=(5, 0))
        
        # 手势控制内容
        gesture_content = ttk.Frame(gesture_frame)
        gesture_content.pack(fill=tk.X, padx=10, pady=10)
        
        # 手势选择
        ttk.Label(gesture_content, text="Current Gesture:", font=('Segoe UI', 10, 'bold')).grid(row=0, column=0, sticky='w', padx=(0, 5))
        gesture_combo = ttk.Combobox(gesture_content, textvariable=self.current_gesture, values=GESTURE_LABELS, width=18, font=('Segoe UI', 9))
        gesture_combo.grid(row=0, column=1, sticky='w', padx=(0, 10))
        
        # 自动采集参数
        ttk.Label(gesture_content, text="Sample Times:", font=('Segoe UI', 10, 'bold')).grid(row=1, column=0, sticky='w', padx=(0, 5), pady=(10, 0))
        times_entry = ttk.Entry(gesture_content, textvariable=self.auto_sample_times, width=5, font=('Consolas', 9))
        times_entry.grid(row=1, column=1, sticky='w', pady=(10, 0), padx=(0, 10))
        
        ttk.Label(gesture_content, text="Pause (sec):", font=('Segoe UI', 10, 'bold')).grid(row=1, column=2, sticky='w', pady=(10, 0), padx=(0, 5))
        pause_entry = ttk.Entry(gesture_content, textvariable=self.auto_pause_var, width=3, font=('Consolas', 9))
        pause_entry.grid(row=1, column=3, sticky='w', pady=(10, 0))
        
        # 自动采集按钮
        self.auto_record_btn = self.create_button(gesture_content, "▶️ Auto Sample", COLORS['success'], command=self.start_auto_recording, state='disabled')
        self.auto_record_btn.grid(row=2, column=0, sticky='w', pady=(10, 0), padx=(0, 5))
        
        self.stop_auto_btn = self.create_button(gesture_content, "⏹️ Stop", COLORS['danger'], command=self.stop_auto_recording, state='disabled')
        self.stop_auto_btn.grid(row=2, column=1, sticky='w', pady=(10, 0))
        
        # 校准区域
        calib_frame = self.create_card(main_container, "Sensor Calibration")
        calib_frame.grid(row=2, column=0, sticky='ew', pady=(0, 10), padx=(0, 5))
        
        # 校准内容
        calib_content = ttk.Frame(calib_frame)
        calib_content.pack(fill=tk.X, padx=10, pady=10)
        
        self.calib_btn = self.create_button(calib_content, "📏 Start Calibration", COLORS['accent'], command=self.toggle_calibration, state='disabled')
        self.calib_btn.grid(row=0, column=0, sticky='w', padx=(0, 5))
        
        self.apply_calib_btn = self.create_button(calib_content, "✅ Apply Calibration", COLORS['success'], command=self.apply_calibration, state='disabled')
        self.apply_calib_btn.grid(row=0, column=1, sticky='w')
        
        calib_status_label = ttk.Label(calib_content, textvariable=self.calib_status_var, font=('Segoe UI', 10, 'bold'), foreground=COLORS['warning'])
        calib_status_label.grid(row=1, column=0, columnspan=2, sticky='w', pady=(10, 0))
        
        # 图表区域
        plot_frame = self.create_card(main_container, "Real-time Data (Calibrated)")
        plot_frame.grid(row=2, column=1, rowspan=2, sticky='nsew', pady=(0, 10))
        
        # 设置网格权重
        main_container.grid_rowconfigure(3, weight=1)
        main_container.grid_columnconfigure(1, weight=1)
        
        # 创建图表
        self.setup_plot_panel(plot_frame)
        
        # 数据显示区域
        data_frame = self.create_card(main_container, "Latest Data (Calibrated + Features)")
        data_frame.grid(row=3, column=0, sticky='nsew', pady=(0, 10), padx=(0, 5))
        
        # 设置数据显示
        self.setup_data_panel(data_frame)
        
        # 底部区域
        bottom_frame = ttk.Frame(main_container)
        bottom_frame.grid(row=4, column=0, columnspan=2, sticky='ew', pady=(0, 5))
        
        # 原始数据区域
        raw_frame = self.create_card(bottom_frame, "Raw Data Stream")
        raw_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 5))
        
        self.setup_raw_data_panel(raw_frame)
        
        # 状态栏
        status_frame = self.create_card(bottom_frame, "Status")
        status_frame.pack(side=tk.LEFT, fill=tk.Y, padx=(5, 0))
        
        self.setup_status_bar(status_frame)
        
        # 初始化串口列表
        self.refresh_ports()
        
        # 设置更新定时器
        self.update_plot()
        self.update_status_info()
    
    def create_card(self, parent, title):
        """创建美化的卡片容器"""
        card = tk.Frame(parent, bg='white', relief='solid', borderwidth=1)
        card.configure(highlightbackground='#dee2e6', highlightthickness=1)
        
        # 卡片标题
        title_label = tk.Label(
            card, text=title, font=('Segoe UI', 12, 'bold'),
            bg='white', fg=COLORS['dark'], anchor='w'
        )
        title_label.pack(fill=tk.X, padx=10, pady=5)
        
        # 分割线
        separator = tk.Frame(card, bg='#dee2e6', height=1)
        separator.pack(fill=tk.X)
        
        return card
    
    def create_button(self, parent, text, bg_color, command=None, state='normal'):
        """创建美化的按钮"""
        btn = tk.Button(
            parent, text=text, font=('Segoe UI', 10, 'bold'),
            bg=bg_color, fg='white', relief='flat',
            bd=0, padx=10, pady=3, cursor='hand2',
            command=command, state=state
        )
        
        # 悬停效果
        def on_enter(e):
            if btn['state'] == 'normal':
                btn.configure(bg=self.darken_color(bg_color))
        
        def on_leave(e):
            if btn['state'] == 'normal':
                btn.configure(bg=bg_color)
        
        btn.bind('<Enter>', on_enter)
        btn.bind('<Leave>', on_leave)
        
        return btn
    
    def darken_color(self, color):
        """颜色加深（用于悬停效果）"""
        if color.startswith('#'):
            color = color.lstrip('#')
            r, g, b = int(color[:2], 16), int(color[2:4], 16), int(color[4:], 16)
            r = max(0, r - 20)
            g = max(0, g - 20)
            b = max(0, b - 20)
            return f'#{r:02x}{g:02x}{b:02x}'
        return color
    
    def setup_plot_panel(self, parent):
        """设置图表面板 - 关键修改：固定Y轴范围为-20到20"""
        plot_container = ttk.Frame(parent)
        plot_container.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # 创建图表
        self.fig = Figure(figsize=(8, 6), dpi=90)
        self.fig.patch.set_facecolor('white')
        
        # 子图
        self.ax1 = self.fig.add_subplot(211)  # 陀螺仪
        self.ax2 = self.fig.add_subplot(212)  # 加速度计
        
        # 样式设置
        for ax in [self.ax1, self.ax2]:
            ax.set_facecolor('#f8f9fa')
            ax.spines['top'].set_visible(False)
            ax.spines['right'].set_visible(False)
            ax.tick_params(labelsize=8, colors='#495057')
            ax.grid(True, alpha=0.3)
            
            # 固定Y轴范围为 -20 到 20
            ax.set_ylim(-20, 20)
            # 关闭自动缩放
            ax.autoscale(enable=False, axis='y')
        
        # 陀螺仪图表
        self.ax1.set_title('Gyroscope (rad/s) - Calibrated', fontsize=10, fontweight='bold')
        self.ax1.set_ylabel('rad/s', fontsize=9)
        self.ax1_lines = {
            'x': self.ax1.plot([], [], '#dc3545', label='X', linewidth=1.2)[0],
            'y': self.ax1.plot([], [], '#198754', label='Y', linewidth=1.2)[0],
            'z': self.ax1.plot([], [], '#0d6efd', label='Z', linewidth=1.2)[0]
        }
        self.ax1.legend(loc='upper right', fontsize=7)
        
        # 加速度计图表
        self.ax2.set_title('Accelerometer (G) - Calibrated', fontsize=10, fontweight='bold')
        self.ax2.set_xlabel('Samples', fontsize=9)
        self.ax2.set_ylabel('G', fontsize=9)
        self.ax2_lines = {
            'x': self.ax2.plot([], [], '#dc3545', label='X', linewidth=1.2)[0],
            'y': self.ax2.plot([], [], '#198754', label='Y', linewidth=1.2)[0],
            'z': self.ax2.plot([], [], '#0d6efd', label='Z', linewidth=1.2)[0]
        }
        self.ax2.legend(loc='upper right', fontsize=7)
        
        # 嵌入图表
        self.canvas = FigureCanvasTkAgg(self.fig, master=plot_container)
        self.canvas.draw()
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
    
    def setup_data_panel(self, parent):
        """设置数据显示面板"""
        data_container = ttk.Frame(parent)
        data_container.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # 创建数据显示标签
        self.data_labels = {}
        channels = [
            ('GX', '#dc3545'), ('GY', '#198754'), ('GZ', '#0d6efd'),
            ('AX', '#dc3545'), ('AY', '#198754'), ('AZ', '#0d6efd'),
            ('ACC_MAG', '#6f42c1'), ('GX_ABS', '#fd7e14'), ('GY_ABS', '#17a2b8'), ('GZ_ABS', '#20c997')
        ]
        
        # 陀螺仪数据
        gyro_label = tk.Label(data_container, text="Gyroscope (rad/s)", font=('Segoe UI', 11, 'bold'), bg='white')
        gyro_label.grid(row=0, column=0, columnspan=3, sticky='w', pady=(0, 5))
        
        # 显示基础数据
        for i, (ch, color) in enumerate(channels[:6]):
            row = (i // 3) + 1
            col = i % 3
            
            card = tk.Frame(data_container, bg='white', relief='solid', borderwidth=1)
            card.grid(row=row, column=col, padx=3, pady=3, sticky='ew')
            
            tk.Label(card, text=f"{ch}", font=('Segoe UI', 9, 'bold'), fg=color, bg='white').pack(pady=(3, 0))
            self.data_labels[ch] = tk.Label(card, text="0.000000", font=('Consolas', 10, 'bold'), bg='white')
            self.data_labels[ch].pack(pady=(0, 3))
        
        # 特征数据
        feat_label = tk.Label(data_container, text="Features", font=('Segoe UI', 11, 'bold'), bg='white')
        feat_label.grid(row=3, column=0, columnspan=4, sticky='w', pady=(10, 5))
        
        feat_frame = tk.Frame(data_container, bg='white')
        feat_frame.grid(row=4, column=0, columnspan=4, sticky='ew')
        
        for i, (ch, color) in enumerate(channels[6:]):
            card = tk.Frame(feat_frame, bg='white', relief='solid', borderwidth=1)
            card.grid(row=0, column=i, padx=3, pady=3, sticky='ew')
            
            tk.Label(card, text=f"{ch}", font=('Segoe UI', 9, 'bold'), fg=color, bg='white').pack(pady=(3, 0))
            self.data_labels[ch] = tk.Label(card, text="0.000000", font=('Consolas', 10, 'bold'), bg='white')
            self.data_labels[ch].pack(pady=(0, 3))
        
        # 设置列权重
        for i in range(3):
            data_container.grid_columnconfigure(i, weight=1)
        for i in range(4):
            feat_frame.grid_columnconfigure(i, weight=1)
    
    def setup_raw_data_panel(self, parent):
        """设置原始数据面板"""
        raw_container = ttk.Frame(parent)
        raw_container.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # 文本框（深色主题）
        text_frame = tk.Frame(raw_container, bg='#1e1e1e')
        text_frame.pack(fill=tk.BOTH, expand=True)
        
        scrollbar = tk.Scrollbar(text_frame, bg='#2d2d2d', troughcolor='#1e1e1e')
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.raw_text = tk.Text(
            text_frame, height=4, font=('Consolas', 9),
            bg='#1e1e1e', fg='#d4d4d4', insertbackground='white',
            wrap=tk.NONE, yscrollcommand=scrollbar.set
        )
        self.raw_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(5, 0), pady=5)
        
        scrollbar.config(command=self.raw_text.yview)
        
        # 控制按钮
        btn_frame = tk.Frame(raw_container, bg='white')
        btn_frame.pack(fill=tk.X, pady=(5, 0))
        
        show_raw_check = tk.Checkbutton(
            btn_frame, text="Show Raw Data", variable=self.show_raw_var,
            font=('Segoe UI', 9), bg='white', fg=COLORS['dark']
        )
        show_raw_check.pack(side=tk.LEFT)
        
        clear_btn = self.create_button(btn_frame, "🧹 Clear", COLORS['light'], command=self.clear_raw_display)
        clear_btn.configure(fg=COLORS['dark'])
        clear_btn.pack(side=tk.RIGHT)
    
    def setup_status_bar(self, parent):
        """设置状态栏"""
        status_container = ttk.Frame(parent)
        status_container.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # 状态项样式
        status_style = {'font': ('Segoe UI', 9), 'bg': 'white', 'anchor': 'w'}
        
        # 记录状态
        tk.Label(status_container, text="Record Status:", font=('Segoe UI', 9, 'bold'), bg='white').grid(row=0, column=0, sticky='w')
        tk.Label(status_container, textvariable=self.record_status_var, fg=COLORS['danger'], **status_style).grid(row=0, column=1, sticky='w', padx=5)
        
        # 自动采集进度
        tk.Label(status_container, text="Auto Sample:", font=('Segoe UI', 9, 'bold'), bg='white').grid(row=1, column=0, sticky='w', pady=(5, 0))
        tk.Label(status_container, textvariable=self.auto_progress_var, fg=COLORS['accent'], **status_style).grid(row=1, column=1, sticky='w', padx=5, pady=(5, 0))
        
        # 当前手势
        tk.Label(status_container, text="Current Gesture:", font=('Segoe UI', 9, 'bold'), bg='white').grid(row=2, column=0, sticky='w', pady=(5, 0))
        tk.Label(status_container, textvariable=self.gesture_status_var, fg=COLORS['accent'], **status_style).grid(row=2, column=1, sticky='w', padx=5, pady=(5, 0))
        
        # 校准状态
        tk.Label(status_container, text="Calibration:", font=('Segoe UI', 9, 'bold'), bg='white').grid(row=3, column=0, sticky='w', pady=(5, 0))
        tk.Label(status_container, textvariable=self.calib_status_display, fg=COLORS['warning'], **status_style).grid(row=3, column=1, sticky='w', padx=5, pady=(5, 0))
        
        # 系统信息
        tk.Label(status_container, text="System Info:", font=('Segoe UI', 9, 'bold'), bg='white').grid(row=4, column=0, sticky='w', pady=(5, 0))
        tk.Label(status_container, textvariable=self.system_info_var, fg=COLORS['dark'], **status_style).grid(row=4, column=1, sticky='w', padx=5, pady=(5, 0))
    
    # ---------------------- 核心功能 ----------------------
    def start_auto_recording(self):
        """开始自动采集 - 修改为缓存模式"""
        try:
            sample_times = int(self.auto_sample_times.get())
            pause_time = int(self.auto_pause_var.get())
            if sample_times <= 0 or sample_times > 100:
                messagebox.showerror("Error", "Sample times must be between 1-100")
                return
            if pause_time < 1 or pause_time > 10:
                messagebox.showerror("Error", "Pause time must be between 1-10 seconds")
                return
        except ValueError:
            messagebox.showerror("Error", "Please enter valid numbers")
            return
        
        # 选择保存文件
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        filename = filedialog.asksaveasfilename(
            defaultextension=".csv",
            filetypes=[("CSV Files", "*.csv"), ("All Files", "*.*")],
            initialfile=f"auto_gesture_{self.current_gesture.get()}_{timestamp}.csv"
        )
        
        if not filename:
            return
        
        # 初始化采集参数
        self.auto_cancelled = False
        self.current_auto_count = 0
        self.auto_sample_times.set(sample_times)
        self.auto_pause_time = pause_time
        
        # ========== 修改：启用缓存模式 ==========
        self.cache_enabled = True
        self.data_cache = []  # 清空缓存
        self.save_filename = filename  # 保存文件名供后续使用
        self.record_counter = 0  # 重置计数器
        
        # 更新UI状态
        self.auto_recording = True
        self.auto_record_btn.config(state='disabled')
        self.stop_auto_btn.config(state='normal')
        self.record_status_var.set(f"⏺️ Auto Sampling - {self.current_gesture.get()} (Caching)")
        self.auto_progress_var.set(f"0/{sample_times} completed")
        
        # 开始第一次采集
        self.add_raw_line(f"[{datetime.now().strftime('%H:%M:%S')}] Start auto sampling {self.current_gesture.get()}, total {sample_times} times (Data caching mode)")
        self.start_single_sample()
    
    def start_single_sample(self):
        """开始单次采集"""
        if self.auto_cancelled or self.current_auto_count >= int(self.auto_sample_times.get()):
            self.finish_auto_recording()
            return
        
        # 弹出倒计时窗口
        countdown_win = CountdownWindow(
            self.root, 
            count=3,
            title=f"Sample {self.current_auto_count+1}/{self.auto_sample_times.get()}"
        )
        self.root.wait_window(countdown_win)
        
        # 如果取消采集
        if countdown_win.cancelled:
            self.auto_cancelled = True
            self.finish_auto_recording()
            return
        
        # 倒计时完成，开始采集
        if countdown_win.finished:
            self.current_auto_count += 1
            self.auto_progress_var.set(f"{self.current_auto_count}/{self.auto_sample_times.get()} completed")
            self.add_raw_line(f"[{datetime.now().strftime('%H:%M:%S')}] Start sampling {self.current_gesture.get()} ({self.current_auto_count}/{self.auto_sample_times.get()})")
            
            # 采集1秒数据
            self.collect_single_gesture_data()
    
    def collect_single_gesture_data(self):
        """采集单次手势数据 - 修改为缓存模式"""
        collect_duration = 1.0
        start_time = time.time()
        temp_buffer = []
        
        while time.time() - start_time < collect_duration and not self.auto_cancelled:
            if self.serial_conn and self.serial_conn.in_waiting:
                line = self.serial_conn.readline().decode('utf-8', errors='ignore').strip()
                if line:
                    data = self.parse_line(line)
                    if data:
                        temp_buffer.append(data)
                        
                        # 直接调用 update_labels 方法（在主线程中执行）
                        self.root.after_idle(self.update_labels, data)
                        # 强制处理UI事件队列，确保立即更新
                        self.root.update_idletasks()
                        
                        # ========== 修改：将数据添加到缓存，不立即写入文件 ==========
                        current_time = datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3]
                        csv_row = [
                            self.record_counter,
                            self.current_auto_count,
                            current_time,
                            self.current_gesture.get(),
                            f"{data['gx']:.6f}",
                            f"{data['gy']:.6f}",
                            f"{data['gz']:.6f}",
                            f"{data['ax']:.6f}",
                            f"{data['ay']:.6f}",
                            f"{data['az']:.6f}",
                            f"{data['gx_calib']:.6f}",
                            f"{data['gy_calib']:.6f}",
                            f"{data['gz_calib']:.6f}",
                            f"{data['ax_calib']:.6f}",
                            f"{data['ay_calib']:.6f}",
                            f"{data['az_calib']:.6f}",
                            f"{data['acc_magnitude']:.6f}",
                            f"{data['gx_abs']:.6f}",
                            f"{data['gy_abs']:.6f}",
                            f"{data['gz_abs']:.6f}",
                            f"{data['gyro_sum']:.6f}"
                        ]
                        
                        # 添加到缓存而不是立即写入
                        self.data_cache.append(csv_row)
                        self.record_counter += 1
                        self.gesture_sample_count += 1
            
            time.sleep(0.005)  # 小延迟避免CPU过载
        
        # 更新缓冲区
        self.data_buffer.extend(temp_buffer)
        
        # 显示缓存统计
        cache_size = len(self.data_cache)
        self.add_raw_line(f"[{datetime.now().strftime('%H:%M:%S')}] Sample {self.current_auto_count} completed, {len(temp_buffer)} samples collected (Total cached: {cache_size})")
        
        # 继续下一次采集
        if self.current_auto_count < int(self.auto_sample_times.get()) and not self.auto_cancelled:
            self.root.after(self.auto_pause_time * 1000, self.start_single_sample)
        else:
            self.finish_auto_recording()
    
    def finish_auto_recording(self):
        """完成自动采集 - 修改为写入缓存数据"""
        self.auto_recording = False
        
        # ========== 修改：写入所有缓存数据到文件 ==========
        if hasattr(self, 'save_filename') and self.save_filename and self.data_cache:
            try:
                # 打开文件并写入所有缓存数据
                with open(self.save_filename, 'w', newline='', encoding='utf-8') as f:
                    csv_writer = csv.writer(f)
                    # 写入表头
                    csv_writer.writerow([
                        'Index', 'Gesture_Index', 'Timestamp', 'Gesture',
                        'GX_Raw', 'GY_Raw', 'GZ_Raw',
                        'AX_Raw', 'AY_Raw', 'AZ_Raw',
                        'GX_Calib', 'GY_Calib', 'GZ_Calib',
                        'AX_Calib', 'AY_Calib', 'AZ_Calib',
                        'Acc_Magnitude', 'GX_Abs', 'GY_Abs', 'GZ_Abs', 'Gyro_Sum'
                    ])
                    # 批量写入所有数据
                    csv_writer.writerows(self.data_cache)
                
                self.add_raw_line(f"[{datetime.now().strftime('%H:%M:%S')}] Data saved to {self.save_filename}, total {len(self.data_cache)} samples")
                
            except Exception as e:
                error_msg = f"Failed to save data: {e}"
                self.add_raw_line(f"[{datetime.now().strftime('%H:%M:%S')}] {error_msg}")
                messagebox.showerror("Save Error", error_msg)
        else:
            if not self.data_cache:
                self.add_raw_line(f"[{datetime.now().strftime('%H:%M:%S')}] No data to save")
        
        # 更新UI
        self.auto_record_btn.config(state='normal')
        self.stop_auto_btn.config(state='disabled')
        
        if self.auto_cancelled:
            total_cached = len(self.data_cache) if hasattr(self, 'data_cache') else 0
            self.record_status_var.set(f"⏹️ Auto Sampling Cancelled")
            self.auto_progress_var.set(f"Cancelled (Completed {self.current_auto_count}/{self.auto_sample_times.get()})")
            self.add_raw_line(f"[{datetime.now().strftime('%H:%M:%S')}] Auto sampling cancelled, {self.current_auto_count} samples completed, {total_cached} samples cached")
        else:
            self.record_status_var.set(f"✅ Auto Sampling Completed")
            self.auto_progress_var.set(f"Completed {self.current_auto_count}/{self.auto_sample_times.get()}")
            self.add_raw_line(f"[{datetime.now().strftime('%H:%M:%S')}] Auto sampling completed! Total {self.record_counter} samples, saved to file")
            messagebox.showinfo("Completed", f"Auto sampling completed!\nGesture: {self.current_gesture.get()}\nTimes: {self.current_auto_count}\nSamples: {self.record_counter}\n\nFile saved to:\n{self.save_filename}")
        
        # 重置计数和缓存
        self.current_auto_count = 0
        self.auto_cancelled = False
        self.cache_enabled = False
        self.data_cache = []  # 清空缓存
        if hasattr(self, 'save_filename'):
            self.save_filename = None
    
    # ---------------------- 辅助功能 ----------------------
    def refresh_ports(self):
        """刷新串口列表"""
        ports = serial.tools.list_ports.comports()
        port_list = [f"{port.device}" for port in ports]
        self.port_combo['values'] = port_list
        if port_list:
            self.port_combo.current(0)
            
    def connect(self):
        """连接串口"""
        if not self.port_var.get():
            messagebox.showerror("Error", "Please select a serial port")
            return
        
        try:
            port = self.port_var.get()
            self.serial_conn = serial.Serial(
                port=port,
                baudrate=115200,
                timeout=0.5,
                bytesize=serial.EIGHTBITS,
                parity=serial.PARITY_NONE,
                stopbits=serial.STOPBITS_ONE
            )
            
            self.running = True
            self.sample_counter = 0
            self.record_counter = 0
            self.status_var.set(f"● Connected to {port}")
            self.auto_record_btn.config(state='normal')
            self.connect_btn.config(state='disabled')
            self.disconnect_btn.config(state='normal')
            self.calib_btn.config(state='normal')
            
            # 启动数据读取线程
            self.read_thread = threading.Thread(target=self.read_data, daemon=True)
            self.read_thread.start()
            
            self.add_raw_line(f"[{datetime.now().strftime('%H:%M:%S')}] Connected to {port}")
            
        except Exception as e:
            messagebox.showerror("Connection Failed", str(e))
    
    def disconnect(self):
        """断开连接"""
        self.running = False
        self.calibrating = False
        self.auto_cancelled = True
        
        if self.auto_recording:
            self.finish_auto_recording()
        
        if self.serial_conn and self.serial_conn.is_open:
            self.serial_conn.close()
        
        self.status_var.set("● Disconnected")
        self.auto_record_btn.config(state='disabled')
        self.stop_auto_btn.config(state='disabled')
        self.connect_btn.config(state='normal')
        self.disconnect_btn.config(state='disabled')
        self.calib_btn.config(state='disabled')
        self.apply_calib_btn.config(state='disabled')
        
        self.add_raw_line(f"[{datetime.now().strftime('%H:%M:%S')}] Disconnected")
    
    def toggle_calibration(self):
        """开始/停止校准"""
        if not self.running:
            messagebox.showwarning("Warning", "Please connect to serial port first")
            return
        
        if not self.calibrating:
            self.calibrating = True
            self.calibration_data.clear()
            self.calib_btn.config(text="🛑 Stop Calibration", bg=COLORS['warning'])
            self.calib_status_var.set("Calibrating...")
            self.add_raw_line(f"[{datetime.now().strftime('%H:%M:%S')}] Start calibration, keep sensor stationary")
        else:
            self.calibrating = False
            self.calib_btn.config(text="📏 Start Calibration", bg=COLORS['accent'])
            self.calib_status_var.set("Calibration Completed (Not Applied)")
            self.apply_calib_btn.config(state='normal')
            self.add_raw_line(f"[{datetime.now().strftime('%H:%M:%S')}] Calibration completed, {len(self.calibration_data)} samples collected")
    
    def apply_calibration(self):
        """应用校准参数"""
        if len(self.calibration_data) < 100:
            messagebox.showwarning("Warning", "Insufficient calibration samples (min 100), recalibrate")
            return
        
        # 计算偏移量
        gx_vals = [d['gx'] for d in self.calibration_data]
        gy_vals = [d['gy'] for d in self.calibration_data]
        gz_vals = [d['gz'] for d in self.calibration_data]
        ax_vals = [d['ax'] for d in self.calibration_data]
        ay_vals = [d['ay'] for d in self.calibration_data]
        az_vals = [d['az'] for d in self.calibration_data]
        
        CALIBRATION_PARAMS['gx_offset'] = np.mean(gx_vals)
        CALIBRATION_PARAMS['gy_offset'] = np.mean(gy_vals)
        CALIBRATION_PARAMS['gz_offset'] = np.mean(gz_vals)
        CALIBRATION_PARAMS['ax_offset'] = np.mean(ax_vals)
        CALIBRATION_PARAMS['ay_offset'] = np.mean(ay_vals)
        CALIBRATION_PARAMS['az_offset'] = np.mean(az_vals)
        
        self.calibrated = True
        self.calib_status_var.set("Calibrated")
        self.calib_status_display.set(f"Calibrated (GX offset: {CALIBRATION_PARAMS['gx_offset']:.6f})")
        self.add_raw_line(f"[{datetime.now().strftime('%H:%M:%S')}] Calibration applied: {CALIBRATION_PARAMS}")
        messagebox.showinfo("Success", "Calibration parameters applied!")
    
    def calculate_features(self, data):
        """计算特征值"""
        acc_magnitude = math.sqrt(data['ax_calib']**2 + data['ay_calib']**2 + data['az_calib']**2)
        gx_abs = abs(data['gx_calib'])
        gy_abs = abs(data['gy_calib'])
        gz_abs = abs(data['gz_calib'])
        
        return {
            'acc_magnitude': acc_magnitude,
            'gx_abs': gx_abs,
            'gy_abs': gy_abs,
            'gz_abs': gz_abs,
            'gyro_sum': gx_abs + gy_abs + gz_abs
        }
    
    def stop_auto_recording(self):
        """停止自动采集"""
        self.auto_cancelled = True
        # 注意：不立即调用 finish_auto_recording，让当前采集完成后再处理
    
    def add_raw_line(self, line):
        """添加原始数据行"""
        if self.show_raw_var.get():
            try:
                self.raw_text.insert('end', line + '\n')
                self.raw_text.see('end')
                # 限制行数
                if float(self.raw_text.index('end-1c')) > 50:
                    self.raw_text.delete(1.0, '2.0')
            except:
                pass
    
    def clear_raw_display(self):
        """清除原始数据显示"""
        self.raw_text.delete(1.0, tk.END)
    
    def parse_line(self, line):
        """解析数据行 - 适配新格式"""
        match = self.pattern.search(line)
        if match:
            try:
                # ========== 关键修改：字段映射 ==========
                # 新格式匹配组顺序：AX, AY, AZ, GX, GY, GZ
                raw_data = {
                    'ax': float(match.group(1)),  # 第一组：AX
                    'ay': float(match.group(2)),  # 第二组：AY
                    'az': float(match.group(3)),  # 第三组：AZ
                    'gx': float(match.group(4)),  # 第四组：GX
                    'gy': float(match.group(5)),  # 第五组：GY
                    'gz': float(match.group(6))   # 第六组：GZ
                }
                # =======================================
                
                # 计算校准后数据
                calib_data = {
                    'gx_calib': raw_data['gx'] - CALIBRATION_PARAMS['gx_offset'],
                    'gy_calib': raw_data['gy'] - CALIBRATION_PARAMS['gy_offset'],
                    'gz_calib': raw_data['gz'] - CALIBRATION_PARAMS['gz_offset'],
                    'ax_calib': raw_data['ax'] - CALIBRATION_PARAMS['ax_offset'],
                    'ay_calib': raw_data['ay'] - CALIBRATION_PARAMS['ay_offset'],
                    'az_calib': raw_data['az'] - CALIBRATION_PARAMS['az_offset']
                }
                
                # 合并数据
                data = {**raw_data, **calib_data}
                # 计算特征
                features = self.calculate_features(data)
                data.update(features)
                
                return data
            except ValueError as e:
                print(f"Conversion error: {e}")
                return None
        return None
    
    def read_data(self):
        """读取数据线程 - 修复数据显示问题"""
        while self.running:
            try:
                if self.serial_conn and self.serial_conn.in_waiting:
                    line = self.serial_conn.readline().decode('utf-8', errors='ignore').strip()
                    if line:
                        # 非自动采集时显示原始数据
                        if not self.auto_recording:
                            self.root.after_idle(self.add_raw_line, line)
                        
                        # 解析数据
                        data = self.parse_line(line)
                        if data:
                            # 如果正在校准，收集校准数据
                            if self.calibrating:
                                self.calibration_data.append(data)
                                if len(self.calibration_data) % 50 == 0:
                                    self.add_raw_line(f"[{datetime.now().strftime('%H:%M:%S')}] Collected {len(self.calibration_data)} calibration samples")
                            
                            # 无论是否自动采集，都更新数据显示面板
                            self.root.after_idle(self.update_labels, data)
                            
                            # 非自动采集时更新缓冲区和计数器
                            if not self.auto_recording:
                                self.data_buffer.append(data)
                                self.sample_counter += 1
                                # 更新系统信息
                                self.root.after_idle(
                                    lambda: self.system_info_var.set(
                                        f"Samples: {self.sample_counter} | Buffer: {len(self.data_buffer)}/500"
                                    )
                                )
                else:
                    time.sleep(0.005)
            except Exception as e:
                print(f"Read error: {e}")
                self.add_raw_line(f"Read error: {e}")
                time.sleep(0.1)
    
    def update_labels(self, data):
        """更新数据显示标签 - 增强调试和错误处理"""
        try:
            # 更新陀螺仪数据
            self.data_labels['GX'].config(text=f"{data['gx_calib']:.6f}")
            self.data_labels['GY'].config(text=f"{data['gy_calib']:.6f}")
            self.data_labels['GZ'].config(text=f"{data['gz_calib']:.6f}")
            
            # 更新加速度计数据
            self.data_labels['AX'].config(text=f"{data['ax_calib']:.6f}")
            self.data_labels['AY'].config(text=f"{data['ay_calib']:.6f}")
            self.data_labels['AZ'].config(text=f"{data['az_calib']:.6f}")
            
            # 更新特征数据
            self.data_labels['ACC_MAG'].config(text=f"{data['acc_magnitude']:.6f}")
            self.data_labels['GX_ABS'].config(text=f"{data['gx_abs']:.6f}")
            self.data_labels['GY_ABS'].config(text=f"{data['gy_abs']:.6f}")
            self.data_labels['GZ_ABS'].config(text=f"{data['gz_abs']:.6f}")
            
        except Exception as e:
            print(f"Update labels error: {e}")
    
    def update_plot(self):
        """更新图表 - 关键修改：移除自动缩放，保持固定Y轴"""
        if len(self.data_buffer) > 1:
            data_list = list(self.data_buffer)
            times = list(range(len(data_list)))
            
            # 更新陀螺仪数据
            gyro_x = [d['gx_calib'] for d in data_list]
            gyro_y = [d['gy_calib'] for d in data_list]
            gyro_z = [d['gz_calib'] for d in data_list]
            
            self.ax1_lines['x'].set_data(times, gyro_x)
            self.ax1_lines['y'].set_data(times, gyro_y)
            self.ax1_lines['z'].set_data(times, gyro_z)
            
            # 更新加速度计数据
            acc_x = [d['ax_calib'] for d in data_list]
            acc_y = [d['ay_calib'] for d in data_list]
            acc_z = [d['az_calib'] for d in data_list]
            
            self.ax2_lines['x'].set_data(times, acc_x)
            self.ax2_lines['y'].set_data(times, acc_y)
            self.ax2_lines['z'].set_data(times, acc_z)
            
            # 只更新X轴范围，保持Y轴固定
            self.ax1.relim()
            self.ax1.autoscale_view(scalex=True, scaley=False)
            self.ax2.relim()
            self.ax2.autoscale_view(scalex=True, scaley=False)
            
            self.canvas.draw_idle()
        
        self.root.after(100, self.update_plot)
    
    def update_status_info(self):
        """更新状态栏信息"""
        self.gesture_status_var.set(f"{self.current_gesture.get()} ({self.gesture_sample_count} samples)")
        self.system_info_var.set(f"Samples: {self.sample_counter} | Buffer: {len(self.data_buffer)}/500")
        self.root.after(1000, self.update_status_info)
    
    def on_closing(self):
        """窗口关闭处理"""
        self.running = False
        self.calibrating = False
        self.auto_cancelled = True
        
        if self.auto_recording:
            # 如果有缓存数据，先保存再关闭
            if hasattr(self, 'data_cache') and self.data_cache:
                self.finish_auto_recording()
            else:
                self.auto_recording = False
        
        if self.serial_conn and self.serial_conn.is_open:
            self.serial_conn.close()
        
        self.root.destroy()


def main():
    root = tk.Tk()
    app = BMI270GUI(root)
    root.protocol("WM_DELETE_WINDOW", app.on_closing)
    root.mainloop()


if __name__ == "__main__":
    main()